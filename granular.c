// granular.c - EFEES "reel to reel": sampler granular de dos cintas (decks A/B) para Nintendo DS/DSi
// (libnds + libfat, ARM9)
//
// Idea: en cada deck la cabeza de lectura avanza sola por el track (siempre en loop) y alrededor
// de ella se disparan granos. Velocidad y pitch son independientes. Un crossfader mezcla los decks.
//
// DOS VISTAS (se pueden intercambiar de pantalla con A o el boton PANTALLAS / PANT.)
//   KNOBS (3 paginas: MEZCLA, NUBE, ESPACIO): carretes de cada deck + perillas
//   ONDAS: una columna vertical por deck (el tiempo corre hacia abajo), crossfader y botones
//   La que este abajo responde al stylus: arrastra un knob hacia arriba/abajo para cambiarlo,
//   toca una pestana para cambiar de pagina, toca la onda para mover la cabeza.
//
// TECLAS
//   START       play / pausa del deck activo        SELECT   cambia de deck activo (A/B)
//   A           intercambia las pantallas           B (mantener)  freeze de la cabeza
//   L / R       crossfader                          X / Y    pagina de knobs anterior / siguiente
//   Izq / Der   elegir knob                         Arr / Abajo   cambiar su valor
//
// LOOP: los dos decks siempre estan en loop (por defecto el track entero). Boton LOOP = modo EDITAR:
// toca y arrastra en la onda con el stylus para delimitar el loop. TODO = loop del track completo.
//
// KNOBS
//   MEZCLA : XFADE, VELOCID (-200..+200 %, por deck), PITCH (+-24 st, por deck), VOLUMEN (3.0x por defecto),
//            ESTEREO, FLUTTER (wow & flutter de cinta)
//   NUBE   : TAMANO, DENSID, SPRAY, DERIVA, ARMONIA, SHIMMER, JITTER, REVERSA
//   ESPACIO: REVERB, COLA, TAPE DLY (delay de cinta de una sola perilla), FILTRO, BARRIDO
// Compresor de salida fijo (4:1) y limitador suave al final.
//
// Audio soportado: MP3 (decodificado en la DS con Helix) y WAV. WAV: PCM 8/16/24 bit, mono o estereo, cualquier frecuencia. Se mezcla a mono,
// se normaliza y se guarda en 8 bit; si no cabe en RAM (la DS tiene 4 MB) se reduce la
// frecuencia de muestreo. La primera carga de cada WAV crea "<archivo>.wav.gr8" en la SD
// (version liviana); las siguientes cargas son casi instantaneas.
// Otros formatos (flac, ogg, m4a...): convertirlos antes en el PC con to_ds.py.

#include <nds.h>
#include <fat.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <dirent.h>
#include <unistd.h>
#include <math.h>
#include "helix/mp3dec.h"

#define OUT_RATE    32768   // lo que pedimos; el hardware corre a ~32728.5 Hz
#define OUT_LEN     4096    // anillo de salida: 4096 muestras = 1 vuelta del timer (DIV_64)
#define CHUNK       256     // muestras que renderizamos por tanda
#define LEAD        2560    // cuanto renderizamos por delante del playhead (~78 ms): colchon contra tirones
#define RESYNC      (LEAD + 3 * CHUNK)   // si el adelanto parece mayor, el playhead nos paso: resincronizar
#define MAX_GRAINS  12
#define WIN_LEN     256

#define DEMO_RATE   16000   // sample de demostracion (suena hasta que cargues un WAV)
#define DEMO_LEN    (DEMO_RATE * 2)

#define MAX_SECS    60      // limite: 1 minuto por deck
#define BUDGET      1200000 // bytes de RAM para el sample (8 bit): 2 min -> ~20 kHz, deja margen de memoria

#define MIX_FULL    (1 << 24)   // mezcla del DROP en Q24: 0 = solo nube, MIX_FULL = solo track limpio

#define VW      256
#define VH      192

// posicion del grano = indice entero (u32) + fraccion de 16 bit; el indice necesita mas de
// 16 bit porque un track de 2 min tiene millones de muestras
typedef struct { u32 ipos; s32 fpos; s32 inc; u32 wpos, winc; s32 pl, pr, amp; bool on, shim; } Grain;

// Un deck = un sample con su propio transporte, nube de granos y voz limpia (DROP).
typedef struct {
    s8 *src, *heapBuf;
    u32 srcLen, srcRate;
    char curName[128];
    bool lostSample;
    s32 posI, posF;                  // cabeza de lectura: indice + fraccion (16 bit)
    bool playing, loopOn, dropOn;
    s32 loopStart, loopEnd;
    s32 mixQ;                        // 0 = solo nube ... MIX_FULL = solo track limpio
    s32 trackI, trackF, trackGate;   // voz limpia
    s32 speedPct, semis, driftW, untilSpawn;
    s32 autoQ, gainC, gainT;
    u32 inc16, cleanInc;
    s32 scanInc;
    Grain grains[MAX_GRAINS];
    u8 pkA[VH], pkB[VH];             // onda vertical: por fila, borde izquierdo / derecho
    s32 reel;                        // angulo de los carretes (Q8, vueltas)
} Deck;

static s16 outL[OUT_LEN] __attribute__((aligned(32)));     // anillos de audio: izquierdo y derecho
static s16 outR[OUT_LEN] __attribute__((aligned(32)));
static s8  demoBuf[DEMO_LEN];        // sample de demostracion
static s16 win[WIN_LEN + 1];         // +1 para interpolar la ventana

static Deck decks[2];
static Deck *dk = &decks[0];         // deck "activo": el que controlan teclas, botones y menu
static int actDeck = 0;
static s32 xfade = 0;                // crossfader 0 = solo A ... 256 = solo B
static s32 xfGainA = 256, xfGainB = 0;
static s32 xgS[2] = { 256 << 8, 0 };    // ganancias suavizadas (Q16) para que mover el crossfader no haga clicks
static s32 grainCap = 8;              // tope de granos por deck; baja solo si la CPU no da abasto   // ganancias de potencia constante (Q8)

static bool touching = false, freezeKey = false;
static bool loopEdit = false;        // modo editar loop: el stylus delimita el loop en la onda
static s32  loopAnchor = 0;
static s32  fadeIdx = 4;
static const float fadeSec[8] = { 0.05f, 0.25f, 0.5f, 1.0f, 2.0f, 4.0f, 8.0f, 16.0f };
static const char *const fadeTxt[8] = { "0.05 s", "0.25 s", "0.5 s", "1 s", "2 s", "4 s", "8 s", "16 s" };

// parametros compartidos
static s32 sizeMs = 120, density = 24, sprayMs = 30;
static s32 driftPct = 0, harmPct = 0, jitterC = 0, revPct = 0;
static s32 revMixPct = 20, decayPct = 60;
static s32 panPct = 80, shimPct = 0, filtPct = 100, sweepPct = 0;
static s32 delayPct = 0;           // delay de cinta: una sola perilla (mezcla + repeticiones)
static s32 flutPct = 0;            // flutter / wow de cinta
static s32 gain = 120;               // volumen de la nube, Q4: 40 = 1.0x, por defecto 3.0x
static s32 normQ = 256;              // compensacion por solapamiento de granos (Q8)
static s32 fadeStep = 1000;          // avance de mixQ por muestra
static s32 harmRatio[4];             // razones Q16 de -12, -5, +7, +12 semitonos

static u32 rng = 2463534242u;
static bool sdOK = false;
static bool browsing = false, touchDrag = false, xfDrag = false;
static int kDrag = -1, kY0 = 0, kDone = 0;          // arrastre de un knob con el stylus     // navegador de la SD abierto / arrastre en la onda

static bool fullRedraw = true;

static void computePeaks(void);
static void audioTick(void);       // mantiene sonando el otro deck mientras se carga       // definida mas abajo (vista)

static u32 rnd(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }
static s32 clampi(s32 v, s32 lo, s32 hi) { return v < lo ? lo : (v > hi ? hi : v); }
static s32 clamp16(s32 v) { return v > 32767 ? 32767 : (v < -32768 ? -32768 : v); }

static u16 rd16(const u8 *p) { return (u16)(p[0] | (p[1] << 8)); }
static u32 rd32(const u8 *p) { return (u32)p[0] | ((u32)p[1] << 8) | ((u32)p[2] << 16) | ((u32)p[3] << 24); }

// ---------------------------------------------------------------- graficos
// Las dos pantallas son bitmaps de 16 bit de 256x192. El texto usa una fuente propia de 6x10.

static u16 *fb;                       // pantalla de abajo (tactil): onda y botones
static u16 *fbTop;                    // pantalla de arriba: parametros / navegador

#define RGB8(r, g, b) ARGB16(1, (r) >> 3, (g) >> 3, (b) >> 3)

// paleta: grises, amarillo claro, blanco y naranja
#define C_DARK     RGB8( 24,  24,  27)
#define C_BG       RGB8( 32,  32,  36)
#define C_PANEL    RGB8( 46,  46,  51)
#define C_PANEL2   RGB8( 62,  62,  69)
#define C_LINE     RGB8( 84,  84,  92)
#define C_GRAY     RGB8(146, 146, 154)
#define C_LGRAY    RGB8(204, 204, 210)
#define C_WHITE    RGB8(255, 255, 255)
#define C_YEL      RGB8(250, 216, 228)      // rosa claro
#define C_YELD     RGB8(176, 138, 154)
#define C_ORG      RGB8(236, 144, 182)      // rosa fuerte
#define C_ORGD     RGB8(150,  92, 120)

#define FONT_W 6
#define FONT_H 10
static const u8 font6[95][FONT_H] = {
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},  //  
    {0x00,0x04,0x04,0x04,0x04,0x04,0x00,0x04,0x00,0x00},  // !
    {0x00,0x0A,0x0A,0x0A,0x00,0x00,0x00,0x00,0x00,0x00},  // "
    {0x00,0x0A,0x0A,0x1F,0x14,0x3E,0x14,0x14,0x00,0x00},  // #
    {0x00,0x04,0x0F,0x14,0x1C,0x07,0x05,0x1E,0x04,0x00},  // $
    {0x00,0x38,0x28,0x3A,0x0C,0x17,0x05,0x07,0x00,0x00},  // %
    {0x00,0x0E,0x08,0x0C,0x15,0x13,0x12,0x0D,0x00,0x00},  // &
    {0x00,0x04,0x04,0x04,0x00,0x00,0x00,0x00,0x00,0x00},  // '
    {0x04,0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x04,0x00},  // (
    {0x08,0x08,0x04,0x04,0x04,0x04,0x04,0x08,0x08,0x00},  // )
    {0x00,0x15,0x0E,0x0E,0x15,0x00,0x00,0x00,0x00,0x00},  // *
    {0x00,0x00,0x04,0x04,0x1F,0x04,0x04,0x00,0x00,0x00},  // +
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x08,0x08,0x08},  // ,
    {0x00,0x00,0x00,0x00,0x00,0x0E,0x00,0x00,0x00,0x00},  // -
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x08,0x00,0x00},  // .
    {0x00,0x01,0x02,0x02,0x04,0x04,0x08,0x08,0x10,0x00},  // /
    {0x00,0x0E,0x11,0x11,0x15,0x11,0x11,0x0E,0x00,0x00},  // 0
    {0x00,0x1C,0x04,0x04,0x04,0x04,0x04,0x1F,0x00,0x00},  // 1
    {0x00,0x0E,0x11,0x01,0x03,0x06,0x08,0x1F,0x00,0x00},  // 2
    {0x00,0x0E,0x11,0x01,0x0E,0x01,0x11,0x0E,0x00,0x00},  // 3
    {0x00,0x02,0x06,0x0A,0x1A,0x1F,0x02,0x02,0x00,0x00},  // 4
    {0x00,0x1E,0x10,0x1E,0x01,0x01,0x01,0x1E,0x00,0x00},  // 5
    {0x00,0x0F,0x18,0x10,0x1E,0x11,0x11,0x0E,0x00,0x00},  // 6
    {0x00,0x1F,0x03,0x02,0x02,0x04,0x04,0x08,0x00,0x00},  // 7
    {0x00,0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E,0x00,0x00},  // 8
    {0x00,0x0E,0x11,0x11,0x0F,0x01,0x03,0x1E,0x00,0x00},  // 9
    {0x00,0x00,0x00,0x08,0x00,0x00,0x00,0x08,0x00,0x00},  // :
    {0x00,0x00,0x00,0x08,0x00,0x00,0x00,0x08,0x08,0x08},  // ;
    {0x00,0x00,0x01,0x0E,0x10,0x0E,0x01,0x00,0x00,0x00},  // <
    {0x00,0x00,0x00,0x3E,0x00,0x3E,0x00,0x00,0x00,0x00},  // =
    {0x00,0x00,0x10,0x0E,0x01,0x0E,0x10,0x00,0x00,0x00},  // >
    {0x00,0x1E,0x02,0x04,0x08,0x08,0x00,0x08,0x00,0x00},  // ?
    {0x00,0x0E,0x09,0x17,0x15,0x15,0x15,0x17,0x08,0x06},  // @
    {0x00,0x04,0x04,0x0A,0x0A,0x0E,0x11,0x11,0x00,0x00},  // A
    {0x00,0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E,0x00,0x00},  // B
    {0x00,0x0F,0x19,0x10,0x10,0x10,0x19,0x0F,0x00,0x00},  // C
    {0x00,0x1E,0x13,0x11,0x11,0x11,0x13,0x1E,0x00,0x00},  // D
    {0x00,0x1F,0x10,0x10,0x1F,0x10,0x10,0x1F,0x00,0x00},  // E
    {0x00,0x1F,0x10,0x10,0x1F,0x10,0x10,0x10,0x00,0x00},  // F
    {0x00,0x0E,0x19,0x10,0x13,0x11,0x19,0x0F,0x00,0x00},  // G
    {0x00,0x11,0x11,0x11,0x1F,0x11,0x11,0x11,0x00,0x00},  // H
    {0x00,0x1F,0x04,0x04,0x04,0x04,0x04,0x1F,0x00,0x00},  // I
    {0x00,0x0E,0x02,0x02,0x02,0x02,0x12,0x0C,0x00,0x00},  // J
    {0x00,0x11,0x12,0x14,0x18,0x14,0x12,0x11,0x00,0x00},  // K
    {0x00,0x10,0x10,0x10,0x10,0x10,0x10,0x1F,0x00,0x00},  // L
    {0x00,0x11,0x1B,0x1B,0x15,0x11,0x11,0x11,0x00,0x00},  // M
    {0x00,0x11,0x19,0x19,0x15,0x13,0x13,0x11,0x00,0x00},  // N
    {0x00,0x0E,0x11,0x11,0x11,0x11,0x11,0x0E,0x00,0x00},  // O
    {0x00,0x1E,0x11,0x11,0x1E,0x10,0x10,0x10,0x00,0x00},  // P
    {0x00,0x0E,0x11,0x11,0x11,0x11,0x11,0x0E,0x03,0x00},  // Q
    {0x00,0x1E,0x11,0x11,0x1E,0x13,0x11,0x10,0x00,0x00},  // R
    {0x00,0x0E,0x11,0x10,0x0E,0x01,0x11,0x0E,0x00,0x00},  // S
    {0x00,0x1F,0x04,0x04,0x04,0x04,0x04,0x04,0x00,0x00},  // T
    {0x00,0x11,0x11,0x11,0x11,0x11,0x11,0x0E,0x00,0x00},  // U
    {0x00,0x11,0x11,0x0A,0x0A,0x0A,0x04,0x04,0x00,0x00},  // V
    {0x00,0x21,0x2D,0x2D,0x1E,0x12,0x12,0x12,0x00,0x00},  // W
    {0x00,0x11,0x0A,0x0A,0x04,0x0A,0x0A,0x11,0x00,0x00},  // X
    {0x00,0x11,0x0A,0x0A,0x04,0x04,0x04,0x04,0x00,0x00},  // Y
    {0x00,0x1F,0x02,0x02,0x04,0x08,0x08,0x1F,0x00,0x00},  // Z
    {0x0C,0x08,0x08,0x08,0x08,0x08,0x08,0x08,0x0C,0x00},  // [
    {0x00,0x10,0x08,0x08,0x04,0x04,0x02,0x02,0x01,0x00},  // backslash
    {0x0C,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x0C,0x00},  // ]
    {0x00,0x08,0x14,0x22,0x00,0x00,0x00,0x00,0x00,0x00},  // ^
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x3F},  // _
    {0x10,0x08,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00},  // `
    {0x00,0x00,0x00,0x1E,0x01,0x0F,0x11,0x1F,0x00,0x00},  // a
    {0x10,0x10,0x10,0x1E,0x11,0x11,0x11,0x1E,0x00,0x00},  // b
    {0x00,0x00,0x00,0x0E,0x10,0x10,0x10,0x0E,0x00,0x00},  // c
    {0x01,0x01,0x01,0x0F,0x11,0x11,0x11,0x0F,0x00,0x00},  // d
    {0x00,0x00,0x00,0x0E,0x11,0x1F,0x10,0x0F,0x00,0x00},  // e
    {0x06,0x08,0x08,0x1E,0x08,0x08,0x08,0x08,0x00,0x00},  // f
    {0x00,0x00,0x00,0x0F,0x11,0x11,0x11,0x0F,0x01,0x0E},  // g
    {0x10,0x10,0x10,0x16,0x19,0x11,0x11,0x11,0x00,0x00},  // h
    {0x04,0x00,0x00,0x0C,0x04,0x04,0x04,0x1F,0x00,0x00},  // i
    {0x04,0x00,0x00,0x1C,0x04,0x04,0x04,0x04,0x04,0x18},  // j
    {0x10,0x10,0x10,0x12,0x14,0x1C,0x12,0x11,0x00,0x00},  // k
    {0x38,0x08,0x08,0x08,0x08,0x08,0x08,0x06,0x00,0x00},  // l
    {0x00,0x00,0x00,0x1F,0x15,0x15,0x15,0x15,0x00,0x00},  // m
    {0x00,0x00,0x00,0x16,0x19,0x11,0x11,0x11,0x00,0x00},  // n
    {0x00,0x00,0x00,0x0E,0x11,0x11,0x11,0x0E,0x00,0x00},  // o
    {0x00,0x00,0x00,0x1E,0x11,0x11,0x11,0x1E,0x10,0x10},  // p
    {0x00,0x00,0x00,0x0F,0x11,0x11,0x11,0x0F,0x01,0x01},  // q
    {0x00,0x00,0x00,0x0F,0x09,0x08,0x08,0x08,0x00,0x00},  // r
    {0x00,0x00,0x00,0x0F,0x10,0x0F,0x01,0x1E,0x00,0x00},  // s
    {0x00,0x08,0x08,0x1E,0x08,0x08,0x08,0x0E,0x00,0x00},  // t
    {0x00,0x00,0x00,0x11,0x11,0x11,0x11,0x0F,0x00,0x00},  // u
    {0x00,0x00,0x00,0x11,0x0A,0x0A,0x0A,0x04,0x00,0x00},  // v
    {0x00,0x00,0x00,0x11,0x15,0x0A,0x0A,0x0A,0x00,0x00},  // w
    {0x00,0x00,0x00,0x1B,0x0A,0x04,0x0A,0x1B,0x00,0x00},  // x
    {0x00,0x00,0x00,0x11,0x0A,0x0A,0x04,0x04,0x04,0x18},  // y
    {0x00,0x00,0x00,0x1F,0x02,0x04,0x08,0x1F,0x00,0x00},  // z
    {0x06,0x04,0x04,0x04,0x18,0x04,0x04,0x04,0x06,0x00},  // {
    {0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04,0x04},  // |
    {0x0C,0x04,0x04,0x04,0x03,0x04,0x04,0x04,0x0C,0x00},  // }
    {0x00,0x00,0x00,0x00,0x1C,0x03,0x00,0x00,0x00,0x00},  // ~
};


static s32 isqrt32(u32 v) {
    u32 r = 0, b = 1u << 30;
    while (b > v) b >>= 2;
    while (b) {
        if (v >= r + b) { v -= r + b; r = (r >> 1) + b; }
        else r >>= 1;
        b >>= 2;
    }
    return (s32)r;
}

static void clearScreen(u16 *s, u16 c) {
    for (int i = 0; i < VW * VH; i++) s[i] = c;
}

static void rect(u16 *s, int x, int y, int w, int h, u16 c) {
    if (x < 0) { w += x; x = 0; }
    if (y < 0) { h += y; y = 0; }
    if (x + w > VW) w = VW - x;
    if (y + h > VH) h = VH - y;
    if (w <= 0 || h <= 0) return;
    for (int j = 0; j < h; j++) {
        u16 *p = s + (y + j) * VW + x;
        for (int i = 0; i < w; i++) p[i] = c;
    }
}

// rectangulo con las esquinas cortadas (1 px)
static void pill(u16 *s, int x, int y, int w, int h, u16 c) {
    rect(s, x + 1, y, w - 2, h, c);
    rect(s, x, y + 1, w, h - 2, c);
}

static int textW(const char *t, int sc) { return (int)strlen(t) * FONT_W * sc; }

static void glyph(u16 *s, int x, int y, int ch, u16 c, int sc) {
    if (ch < 32 || ch > 126) ch = '?';
    if (x < 0 || y < 0 || x + FONT_W * sc > VW || y + FONT_H * sc > VH) return;
    const u8 *g = font6[ch - 32];
    for (int r = 0; r < FONT_H; r++) {
        u8 bits = g[r];
        if (!bits) continue;
        for (int k = 0; k < FONT_W; k++) {
            if (!(bits & (0x20 >> k))) continue;
            if (sc == 1) s[(y + r) * VW + x + k] = c;
            else         rect(s, x + k * sc, y + r * sc, sc, sc, c);
        }
    }
}

static void text(u16 *s, int x, int y, const char *t, u16 c, int sc) {
    for (; *t; t++, x += FONT_W * sc) glyph(s, x, y, (unsigned char)*t, c, sc);
}

// tecla en naranja + descripcion en gris; avanza x
static void keyHint(int *x, int y, const char *key, const char *label) {
    text(fbTop, *x, y, key, C_ORG, 1);
    *x += textW(key, 1) + 4;
    text(fbTop, *x, y, label, C_GRAY, 1);
    *x += textW(label, 1) + 10;
}

static void drawHeader(const char *a, const char *b, u16 ca) {
    rect(fbTop, 0, 0, VW, 16, C_PANEL);
    rect(fbTop, 0, 0, 4, 16, C_ORG);
    text(fbTop, 10, 3, a, ca, 1);
    if (b) text(fbTop, 10 + textW(a, 1) + 8, 3, b, C_LGRAY, 1);
}

// pantallas de carga / error (arriba)
static void drawLoadScreen(const char *name) {
    clearScreen(fbTop, C_BG);
    drawHeader("CARGANDO", NULL, C_YEL);
    char t[36];
    snprintf(t, sizeof t, "%.34s", name);
    text(fbTop, 8, 40, t, C_WHITE, 1);
    rect(fbTop, 8, 62, 240, 8, C_PANEL2);
    text(fbTop, 8, 120, "B = cancelar", C_GRAY, 1);
}

static void drawLoadBar(int pct) {
    if (pct < 0) pct = 0;
    if (pct > 100) pct = 100;
    rect(fbTop, 8, 62, 240 * pct / 100, 8, C_ORG);
    char t[8];
    snprintf(t, sizeof t, "%3d%%", pct);
    rect(fbTop, 8, 76, 40, 10, C_BG);
    text(fbTop, 8, 76, t, C_YEL, 1);
}

static void drawLoadNote(const char *note) {
    rect(fbTop, 8, 92, 240, 10, C_BG);
    text(fbTop, 8, 92, note, C_GRAY, 1);
}

static void drawErrorScreen(const char *msg) {
    clearScreen(fbTop, C_BG);
    drawHeader("ERROR", NULL, C_ORG);
    char t[38];
    snprintf(t, sizeof t, "%.36s", msg);
    text(fbTop, 8, 40, t, C_WHITE, 1);
    int x = 8;
    keyHint(&x, 176, "A", "volver");
}

// ---------------------------------------------------------------- reverb (Schroeder: 4 combs + 2 allpass)
typedef struct { s16 *buf; u32 len, idx; s32 lp; } Comb;
static s16 cb0[1789], cb1[1999], cb2[2237], cb3[2459], ab0[557], ab1[421], ab2[509], ab3[379];
static Comb combs[4] = { { cb0, 1789, 0, 0 }, { cb1, 1999, 0, 0 }, { cb2, 2237, 0, 0 }, { cb3, 2459, 0, 0 } };
static Comb aps[2]   = { { ab0, 557, 0, 0 }, { ab1, 421, 0, 0 } };
static Comb apsR[2]  = { { ab2, 509, 0, 0 }, { ab3, 379, 0, 0 } };
static s32 revMix = 51, revFb = 220, revDamp = 80;      // Q8

static void updateReverb(void) {
    decayPct = 45 + revMixPct * 50 / 100;               // una sola perilla: mas reverb = mas mezcla y mas cola
    revMix = revMixPct * 256 / 100;
    revFb  = 179 + decayPct * 69 / 100;                  // 0.70 .. 0.97
}

static u32 revIdle = 0;
static void revClear(void) {
    memset(cb0, 0, sizeof cb0); memset(cb1, 0, sizeof cb1); memset(cb2, 0, sizeof cb2); memset(cb3, 0, sizeof cb3);
    memset(ab0, 0, sizeof ab0); memset(ab1, 0, sizeof ab1); memset(ab2, 0, sizeof ab2); memset(ab3, 0, sizeof ab3);
    for (int i = 0; i < 4; i++) { combs[i].lp = 0; }
}

static s32 apRun(Comb *a, s32 w) {                       // difusion (allpass)
    s32 z = a->buf[a->idx];
    s32 v = clamp16(w + (z >> 1));
    a->buf[a->idx] = (s16)v;
    if (++a->idx >= a->len) a->idx = 0;
    return z - (v >> 1);
}

// entrada mono (suma de L y R); los 4 combs se mezclan con signos distintos para cada oido,
// asi la cola sale ancha y descorrelacionada
static void reverbProcess(s32 inL, s32 inR, s32 *wl, s32 *wr) {
    s32 x = (((inL + inR) >> 1) * (256 - revFb)) >> 8;   // compensa la ganancia de la realimentacion
    s32 y[4];
    for (int i = 0; i < 4; i++) {
        Comb *c = &combs[i];
        y[i] = c->buf[c->idx];
        c->lp += ((y[i] - c->lp) * revDamp) >> 8;        // amortiguacion: la cola se oscurece
        c->buf[c->idx] = (s16)clamp16(x + ((c->lp * revFb) >> 8));
        if (++c->idx >= c->len) c->idx = 0;
    }
    s32 l = (y[0] - y[1] + y[2] - y[3]) >> 2;
    s32 r = (y[0] + y[1] - y[2] - y[3]) >> 2;
    l = apRun(&aps[1], apRun(&aps[0], l));
    r = apRun(&apsR[1], apRun(&apsR[0], r));
    *wl = l; *wr = r;
}

// ---------------------------------------------------------------- motor
// Volumen automatico: el sample ya esta normalizado por su pico, pero la musica real tiene
// mucho mas pico que promedio y suena bajito. Medimos el RMS y subimos hasta ~-9 dBFS
// (maximo +16 dB); el limitador suave de la salida se encarga de los picos.
static void computeAuto(void) {
    u64 sum = 0;
    u32 n = 0, step = dk->srcLen > 200000 ? 4 : 1;
    for (u32 i = 0; i < dk->srcLen; i += step) { s32 v = dk->src[i]; sum += (u32)(v * v); n++; }
    s32 rms = n ? isqrt32((u32)(sum / n)) : 1;
    if (rms < 1) rms = 1;
    s32 q = 44 * 256 / rms;
    if (q < 256) q = 256;
    if (q > 1664) q = 1664;
    dk->autoQ = q;
}

static void updateIncOne(void) {
    dk->gainC = (gain * dk->autoQ) >> 8;
    dk->gainT = (((gain * 2) / 5) * dk->autoQ) >> 8;
    float base = (float)dk->srcRate / 32728.5f;                    // frecuencia del sample -> salida
    dk->inc16    = (u32)(65536.0f * base * exp2f(dk->semis / 12.0f));
    dk->cleanInc = (u32)(65536.0f * base);
    dk->scanInc  = (s32)(65536.0f * base * (dk->speedPct / 100.0f));
    float ov = (float)density * (float)sizeMs / 1000.0f;       // granos solapados en promedio
    normQ    = (s32)(256.0f / sqrtf(ov < 1.0f ? 1.0f : ov));
    fadeStep = (s32)((float)MIX_FULL / (fadeSec[fadeIdx] * 32728.5f));
    if (fadeStep < 1) fadeStep = 1;
}

static void updateInc(void) {                                   // los parametros compartidos tocan a los dos decks
    Deck *keep = dk;
    for (int i = 0; i < 2; i++) { dk = &decks[i]; updateIncOne(); }
    dk = keep;
}

static void setXfade(s32 v) {
    xfade = clampi(v, 0, 256);
    float a = 1.5707963f * (float)xfade / 256.0f;
    xfGainA = (s32)(256.0f * cosf(a) + 0.5f);
    xfGainB = (s32)(256.0f * sinf(a) + 0.5f);
}

static void killGrains(void) {
    for (int g = 0; g < MAX_GRAINS; g++) dk->grains[g].on = false;
    dk->untilSpawn = 1;
}

static s32 minLoop(void) { s32 m = (s32)(dk->srcLen / 4); return m > 2000 ? 2000 : m; }

static void resetTransport(bool autoplay, bool loop) {
    dk->posI = 0; dk->posF = 0;
    dk->loopStart = 0; dk->loopEnd = (s32)dk->srcLen - 1;
    dk->loopOn = true;                           // siempre en loop
    dk->playing = autoplay;
    dk->dropOn = false; dk->mixQ = 0; dk->trackI = 0; dk->trackF = 0; dk->driftW = 0;
    killGrains();
}

static void seekTo(s32 idx) {
    dk->posI = clampi(idx, 0, (s32)dk->srcLen - 1);
    dk->posF = 0;
}

static void togglePlay(void) {
    if (!dk->playing) {
        if (!dk->dropOn && !dk->loopOn && dk->posI >= (s32)dk->srcLen - 2) seekTo(0);   // estaba al final: vuelve a empezar
        dk->playing = true;
    } else {
        dk->playing = false;
    }
}

static void fixLoop(bool movedStart) {
    if (dk->loopStart < 0) dk->loopStart = 0;
    if (dk->loopEnd > (s32)dk->srcLen - 1) dk->loopEnd = (s32)dk->srcLen - 1;
    s32 m = minLoop();
    if (dk->loopEnd - dk->loopStart < m) {
        if (movedStart) {
            dk->loopEnd = dk->loopStart + m;
            if (dk->loopEnd > (s32)dk->srcLen - 1) { dk->loopEnd = (s32)dk->srcLen - 1; dk->loopStart = dk->loopEnd - m; }
        } else {
            dk->loopStart = dk->loopEnd - m;
            if (dk->loopStart < 0) { dk->loopStart = 0; dk->loopEnd = m; }
        }
    }
}

static void toggleLoop(void) {
    loopEdit = !loopEdit;
}

// avanza la cabeza una muestra de salida
static inline void advancePos(void) {
    dk->posF += dk->scanInc;
    dk->posI += dk->posF >> 16;
    dk->posF &= 0xFFFF;
    if (dk->loopOn) {
        if (dk->scanInc > 0 && dk->posI >= dk->loopEnd) {
            dk->posI = dk->loopStart + (dk->posI - dk->loopEnd);
            if (dk->posI >= dk->loopEnd) dk->posI = dk->loopStart;
        } else if (dk->scanInc < 0 && dk->posI < dk->loopStart) {
            dk->posI = dk->loopEnd - (dk->loopStart - dk->posI);
            if (dk->posI < dk->loopStart) dk->posI = dk->loopEnd - 1;
        }
    } else if (dk->posI >= (s32)dk->srcLen - 1) {
        dk->posI = (s32)dk->srcLen - 1; dk->posF = 0; dk->playing = false;      // fin del track
    } else if (dk->posI < 0) {
        dk->posI = 0; dk->posF = 0; dk->playing = false;
    }
}

// ---- delay estereo ping-pong (1 s maximo por lado)
#define DLY_LEN   32768
#define DLY_MASK  (DLY_LEN - 1)
static s16 dlyL[DLY_LEN], dlyR[DLY_LEN];
static u32 dW = 0;
static s32 dtCur = 0, dtTgt = 0;              // tiempo actual / objetivo en muestras Q8 (el actual se desliza)
static s32 dFb = 115, dMix = 0, dLpL = 0, dLpR = 0;

#define DLY_TIME_MS 420                       // un tape delay: tiempo fijo, lo que cambia es cuanto se repite
static void updateDelay(void) {
    dtTgt = (s32)((float)DLY_TIME_MS * 32.7285f * 256.0f);
    dFb   = 70 + delayPct * 130 / 100;        // 0.27 .. 0.78
    dMix  = delayPct * 230 / 100;             // hasta 0.9
}

// ---- wow & flutter de cinta: LFOs lentos + una linea de retardo corta (vibrato) en la salida
#define WOW_INC  72180u                       // 0.55 Hz
#define FL1_INC  826800u                      // 6.3 Hz
#define FL2_INC  1194400u                     // 9.1 Hz
#define VB_LEN   256
static s16 vbL[VB_LEN], vbR[VB_LEN];
static u32 vbW = 0, phWow = 0, phFl1 = 0, phFl2 = 0;
static s32 wowAmp = 0, flAmp = 0;             // profundidad en muestras
static void updateFlutter(void) { wowAmp = flutPct * 90 / 100; flAmp = flutPct * 14 / 100; }

// seno parabolico: ph (32 bit = una vuelta) -> -32768..32767
static s32 lfoSin(u32 ph) {
    s32 x = (s32)(s16)(ph >> 16);
    s32 ax = x < 0 ? -x : x;
    return (x * (32768 - ax)) >> 13;
}

// compresor fijo de la salida (4:1 sobre -12 dBFS, ataque ~2 ms, suelta ~150 ms) con ganancia de compensacion
#define COMP_T 8000
static s32 cEnv = 0, cG = 32768, cTgt = 32768;

// ---- estereo, shimmer y filtro
static s32 sinT[64];                                   // Q8: seno en 64 pasos (para carretes y knobs)
static s32 panTab[33];                        // ganancias Q8 de potencia constante (centro = 256 en cada oido)
static s32 shimRatio[4];                      // razones Q16 de +12, +24, +19 y -12 semitonos
static s32 aTab[128], fcHz[128];              // coeficiente (Q15) y frecuencia del filtro por paso
static s32 fS[2][2];                          // estados del filtro (L, R) de 2 polos
static s32 aCur = 32768, aTgt = 32768;
static u32 lfoPh = 0, shPh = 0;               // fases: barrido del filtro (~12 s) y fundido del shimmer (~17 s)
static u32 fCnt = 0;
#define LFO_INC   10938u                      // 2^32 / (12 s * 32728.5 Hz)
#define SHIM_INC  7720u                       // 2^32 / (17 s * 32728.5 Hz)

static void initTables(void) {
    for (int i = 0; i < 64; i++) sinT[i] = (s32)(256.0f * sinf(6.2831853f * (float)i / 64.0f));
    for (int i = 0; i <= 32; i++) panTab[i] = (s32)(362.0f * cosf((float)i * 3.14159265f / 64.0f));
    shimRatio[0] = (s32)(65536.0f * exp2f(12.0f / 12.0f));
    shimRatio[1] = (s32)(65536.0f * exp2f(24.0f / 12.0f));
    shimRatio[2] = (s32)(65536.0f * exp2f(19.0f / 12.0f));
    shimRatio[3] = (s32)(65536.0f * exp2f(-12.0f / 12.0f));
    for (int c = 0; c < 128; c++) {
        float fc = 40.0f * exp2f((float)c * 7.81f / 127.0f);       // 40 Hz .. ~9 kHz
        float a = 1.0f - expf(-6.2831853f * fc / 32728.5f);
        fcHz[c] = (s32)fc;
        aTab[c] = (s32)(32768.0f * a);
    }
}

// triangulo suavizado 0..256 a partir de una fase de 32 bit
static s32 smooth01(u32 ph) {
    u32 t = ph < 0x80000000u ? ph : ~ph;
    s32 x = (s32)(t >> 16);
    if (x > 32767) x = 32767;
    s32 x2 = (x * x) >> 15;
    s32 v = 3 * x2 - ((2 * x2 * x) >> 15);
    return v >> 7;
}

static void filterTarget(void) {
    if (filtPct >= 100 && !sweepPct) { aTgt = 32768; return; }
    s32 c = filtPct * 127 / 100;
    if (sweepPct) c -= sweepPct * smooth01(lfoPh) / 256;       // el barrido baja el corte desde el valor fijado
    aTgt = aTab[clampi(c, 0, 127)];
}

static inline s32 lp2(s32 *st, s32 x) {
    st[0] += (((x - st[0]) >> 3) * aCur) >> 12;
    st[1] += (((st[0] - st[1]) >> 3) * aCur) >> 12;
    return st[1];
}

static void spawn(void) {
    int act = 0;
    for (int g = 0; g < MAX_GRAINS; g++) act += dk->grains[g].on;
    if (act >= grainCap) return;                 // CPU justa: no abrir mas granos
    for (int g = 0; g < MAX_GRAINS; g++) {
        if (dk->grains[g].on) continue;
        s32 sp = (s32)(sprayMs * dk->srcRate / 1000);
        s32 start = dk->posI + (s32)(rnd() % (u32)(2 * sp + 1)) - sp;
        if (driftPct) {                                           // deriva: caminata aleatoria con retorno suave
            s32 step = (s32)(driftPct * dk->srcRate / 1000);
            dk->driftW += (s32)(rnd() % (u32)(2 * step + 1)) - step;
            dk->driftW -= dk->driftW / 32;
            start += dk->driftW;
        }
        s32 inc = (s32)dk->inc16, amp = 256;
        bool shim = false;
        if (shimPct) {                                            // shimmer: octavas que suben y bajan de a poco
            s32 env = smooth01(shPh);
            if ((s32)(rnd() % 100) < shimPct * env / 256) {
                u32 r = rnd() % 100;
                inc = (s32)(((u64)(u32)inc * (u32)shimRatio[r < 55 ? 0 : (r < 80 ? 1 : (r < 92 ? 2 : 3))]) >> 16);
                amp = 64 + env * 192 / 256;
                shim = true;
            }
        }
        if (!shim && harmPct && (rnd() % 100) < (u32)harmPct)     // armonia: grano transpuesto
            inc = (s32)(((u64)(u32)inc * (u32)harmRatio[rnd() & 3]) >> 16);
        if (jitterC) {                                            // desafinacion aleatoria en cents
            s32 j = (s32)(rnd() % (u32)(2 * jitterC + 1)) - jitterC;
            inc += (inc * j) / 1731;
        }
        u32 len = (u32)(sizeMs * OUT_RATE / 1000);
        if (shim) len += len >> 1;                                // los granos shimmer son mas largos
        if (revPct && (rnd() % 100) < (u32)revPct) {              // grano al reves: parte del final
            start += (s32)(((len >> 4) * ((u32)inc >> 4)) >> 8);
            inc = -inc;
        }
        start = clampi(start, 0, (s32)dk->srcLen - 2);
        s32 span = panPct * 16 / 100;                             // panorama: posicion 0..32, centro 16
        s32 pp = 16 + (s32)(rnd() % (u32)(2 * span + 1)) - span;
        dk->grains[g].ipos = (u32)start;
        dk->grains[g].fpos = 0;
        dk->grains[g].inc  = inc;
        dk->grains[g].wpos = 0;
        dk->grains[g].winc = ((u32)WIN_LEN << 16) / len;
        dk->grains[g].pl   = panTab[pp];
        dk->grains[g].pr   = panTab[32 - pp];
        dk->grains[g].amp  = amp;
        dk->grains[g].shim = shim;
        dk->grains[g].on   = true;
        return;
    }
}

// limitador suave: lineal hasta 16384 y luego comprime hacia 32767 (sin clipping duro)
static s32 softClip(s32 x) {
    s32 a = x < 0 ? -x : x;
    if (a > 16384) {
        s32 d = a - 16384;
        if (d > 65535) d = 65535;
        a = 16384 + (d * 16383) / (d + 16383);
    }
    return x < 0 ? -a : a;
}

// todo en enteros: el ARM9 no tiene FPU
#define SCALE(v) ((((v) * normQ >> 8) * dk->gainC) >> 4)

// un deck: nube de granos (directo + envio a la reverb) y voz limpia; xg = ganancia del crossfader (Q8)
static void deckRender(Deck *d, s32 xg, s32 *oDL, s32 *oDR, s32 *oSL, s32 *oSR, s32 *oT) {
    dk = d;
    *oDL = *oDR = *oSL = *oSR = *oT = 0;
    if (dk->dropOn) {
        if (dk->mixQ < MIX_FULL) {
            dk->mixQ += fadeStep;
            if (dk->mixQ >= MIX_FULL) { dk->mixQ = MIX_FULL; killGrains(); }   // la nube ya no se oye: no gasta CPU
        }
    } else if (dk->mixQ > 0) {
        dk->mixQ -= fadeStep;
        if (dk->mixQ < 0) dk->mixQ = 0;
    }

    s32 dL = 0, dR = 0, sL = 0, sR = 0;
    if (dk->mixQ < MIX_FULL) {
        if (dk->playing && !(touching && d == &decks[actDeck]) && !(freezeKey && d == &decks[actDeck])) advancePos();
        if (xg < 2) {
            killGrains();                               // deck apagado por el crossfader: solo avanza la cinta
        } else {
            if (dk->playing || (touching && d == &decks[actDeck])) {
                if (--dk->untilSpawn <= 0) { spawn(); dk->untilSpawn = OUT_RATE / density; }
            }
            s32 aL = 0, aR = 0, zL = 0, zR = 0;
            for (int g = 0; g < MAX_GRAINS; g++) {
                Grain *gr = &dk->grains[g];
                if (!gr->on) continue;
                u32 si = gr->ipos;
                if (si >= dk->srcLen - 1 || gr->wpos >= ((u32)WIN_LEN << 16)) { gr->on = false; continue; }
                s32 a = dk->src[si], b = dk->src[si + 1];
                s32 s = a + (((b - a) * (gr->fpos >> 8)) >> 8);        // interpolacion lineal
                u32 wi = gr->wpos >> 16;
                s32 w = win[wi] + (((win[wi + 1] - win[wi]) * (s32)((gr->wpos >> 8) & 0xFF)) >> 8);
                s32 v = (((s * w) >> 7) * gr->amp) >> 8;                // s8 -> s16 con ventana Q15
                s32 vl = (v * gr->pl) >> 8, vr = (v * gr->pr) >> 8;
                if (gr->shim) { zL += vl; zR += vr; } else { aL += vl; aR += vr; }
                s32 f = gr->fpos + gr->inc;
                gr->ipos += (u32)(f >> 16);
                gr->fpos  = f & 0xFFFF;
                gr->wpos += gr->winc;
            }
            // el shimmer se oye poco directo y mucho dentro de la reverb
            dL = clampi(SCALE(aL + ((zL * 90) >> 8)), -262143, 262143);   // el limite lo pone el compresor de salida
            dR = clampi(SCALE(aR + ((zR * 90) >> 8)), -262143, 262143);
            sL = softClip(SCALE(aL + zL + (zL >> 1)));
            sR = softClip(SCALE(aR + zR + (zR >> 1)));
        }
    }
    s32 fadeG = ((32768 - (dk->mixQ >> 9)) * xg) >> 8;             // Q15: fundido del DROP x crossfader
    *oDL = ((dL >> 3) * fadeG) >> 12; *oDR = ((dR >> 3) * fadeG) >> 12;
    *oSL = (sL * fadeG) >> 15; *oSR = (sR * fadeG) >> 15;

    // voz limpia: el track tal cual, 1x, sin pitch, sin granos
    if (dk->dropOn || dk->mixQ > 0) {
        if (dk->playing) { dk->trackGate += 50; if (dk->trackGate > 32768) dk->trackGate = 32768; }
        else if (dk->trackGate > 0) { dk->trackGate -= 50; if (dk->trackGate < 0) dk->trackGate = 0; }
        if (dk->playing || dk->trackGate > 0) {
            u32 ti = (u32)dk->trackI;
            if (ti >= dk->srcLen - 1) {                                 // fin de la cancion
                dk->dropOn = false; dk->posI = (s32)dk->srcLen - 1; dk->posF = 0; dk->playing = false;
            } else {
                s32 a = dk->src[ti], b = dk->src[ti + 1];
                s32 s = a + (((b - a) * (dk->trackF >> 8)) >> 8);
                s32 x = ((s * 256 * dk->gainT) >> 4);
                if (x > 262143) x = 262143;                              // con mucha ganancia automatica: evita desbordar el producto
                if (x < -262143) x = -262143;
                s32 tr = (x * (dk->trackGate >> 3)) >> 12;
                tr = (tr * (dk->mixQ >> 12)) >> 12;                     // el fundido sube el track mientras baja la nube
                *oT = (tr * xg) >> 8;
                dk->trackF += (s32)dk->cleanInc;
                dk->trackI += dk->trackF >> 16;
                dk->trackF &= 0xFFFF;
            }
        }
    }
}

static void render(s16 *dstL, s16 *dstR, int n) {
    Deck *keep = dk;
    for (int i = 0; i < n; i++) {
        lfoPh += LFO_INC;
        shPh  += SHIM_INC;
        if ((++fCnt & 31) == 0) filterTarget();
        aCur += (aTgt - aCur) >> 6;
        phWow += WOW_INC; phFl1 += FL1_INC; phFl2 += FL2_INC;

        s32 dL[2], dR[2], sL[2], sR[2], tr[2];
        xgS[0] += ((xfGainA << 8) - xgS[0]) >> 8;
        xgS[1] += ((xfGainB << 8) - xgS[1]) >> 8;
        deckRender(&decks[0], xgS[0] >> 8, &dL[0], &dR[0], &sL[0], &sR[0], &tr[0]);
        deckRender(&decks[1], xgS[1] >> 8, &dL[1], &dR[1], &sL[1], &sR[1], &tr[1]);

        // reverb estereo sobre las dos nubes
        s32 wl, wr;
        if (revMix > 0) revIdle = 0; else if (revIdle < 100000) revIdle++;
        if (revIdle == 99999) revClear();                          // sin reverb por ~3 s: se vacia y deja de gastar CPU
        if (revIdle < 99999) reverbProcess(clamp16(sL[0] + sL[1]), clamp16(sR[0] + sR[1]), &wl, &wr);
        else wl = wr = 0;
        s32 cmL = ((dL[0] + dL[1]) * (256 - (revMix >> 1)) + wl * revMix) >> 8;
        s32 cmR = ((dR[0] + dR[1]) * (256 - (revMix >> 1)) + wr * revMix) >> 8;
        s32 trk = tr[0] + tr[1];
        s32 tr_ = trk;
        // delay ping-pong: entra mono por la izquierda y cada eco rebota al otro lado
        s32 oL = cmL + tr_, oR = cmR + tr_;
        if (dtCur < dtTgt)      { dtCur += 96; if (dtCur > dtTgt) dtCur = dtTgt; }
        else if (dtCur > dtTgt) { dtCur -= 96; if (dtCur < dtTgt) dtCur = dtTgt; }
        if (dMix > 0 || dLpL > 2 || dLpL < -2 || dLpR > 2 || dLpR < -2) {
            s32 sw = lfoSin(phWow), sf = lfoSin(phFl1);
            s32 dt = dtCur + ((sw * 2500 + sf * 600) >> 15);          // la cinta no gira pareja
            s32 dn = dt >> 8, df = dt & 255;
            u32 r0 = (dW - (u32)dn) & DLY_MASK, r1 = (r0 - 1) & DLY_MASK;
            s32 eL = dlyL[r0] + (((dlyL[r1] - dlyL[r0]) * df) >> 8);
            s32 eR = dlyR[r0] + (((dlyR[r1] - dlyR[r0]) * df) >> 8);
            // cada repeticion se oscurece y se satura un poco, como en la cinta
            dLpL += ((softClip((eR * dFb) >> 8) - dLpL) * 100) >> 8;
            dLpR += ((softClip((eL * dFb) >> 8) - dLpR) * 100) >> 8;
            dlyL[dW] = (s16)clamp16(softClip((oL + oR) >> 1) + dLpL);
            dlyR[dW] = (s16)clamp16(dLpR);
            dW = (dW + 1) & DLY_MASK;
            oL += (eL * dMix) >> 8;
            oR += (eR * dMix) >> 8;
        } else {                                                    // apagado: el buffer se vacia sin gastar CPU
            dlyL[dW] = dlyR[dW] = 0; dLpL = dLpR = 0;
            dW = (dW + 1) & DLY_MASK;
        }

        // flutter: vibrato leve y siempre presente en la linea corta (profundidad 0 = sin modulacion)
        vbL[vbW] = (s16)clamp16(oL); vbR[vbW] = (s16)clamp16(oR);
        {
            s32 md = (lfoSin(phWow) * wowAmp + ((lfoSin(phFl1) + lfoSin(phFl2)) >> 1) * flAmp) >> 7;   // Q8 muestras
            s32 d = 128 * 256 + md;
            s32 dn = d >> 8, df = d & 255;
            u32 r0 = (vbW - (u32)dn) & (VB_LEN - 1), r1 = (r0 - 1) & (VB_LEN - 1);
            oL = vbL[r0] + (((vbL[r1] - vbL[r0]) * df) >> 8);
            oR = vbR[r0] + (((vbR[r1] - vbR[r0]) * df) >> 8);
            vbW = (vbW + 1) & (VB_LEN - 1);
        }

        // filtro pasa-bajos de toda la salida (con el filtro abierto solo sigue la senal, sin gastar)
        if (aCur >= 32700 && aTgt >= 32768) {
            fS[0][0] = fS[0][1] = oL;
            fS[1][0] = fS[1][1] = oR;
        } else {
            oL = lp2(fS[0], oL);
            oR = lp2(fS[1], oR);
        }
        // compresor de salida (fijo)
        {
            s32 pk = oL < 0 ? -oL : oL, pr = oR < 0 ? -oR : oR;
            if (pr > pk) pk = pr;
            if (pk > 262143) pk = 262143;
            if (pk > cEnv) cEnv += (pk - cEnv) >> 6; else cEnv -= (cEnv >> 12) + 1;
            if (cEnv < 0) cEnv = 0;
            if ((i & 7) == 0)
                cTgt = cEnv > COMP_T ? (s32)((((u32)(3 * COMP_T + cEnv)) << 13) / (u32)cEnv) : 32768;
            cG += (cTgt - cG) >> 5;
            oL = clampi(oL, -262143, 262143); oR = clampi(oR, -262143, 262143);
            oL = (((oL >> 3) * cG) >> 12) * 358 >> 8;               // x1.4 de compensacion
            oR = (((oR >> 3) * cG) >> 12) * 358 >> 8;
        }
        dstL[i] = (s16)clamp16(softClip(oL));                   // limitador suave al final
        dstR[i] = (s16)clamp16(softClip(oR));
    }
    dk = keep;
}

// ---------------------------------------------------------------- sample
static void freeHeap(void) { if (dk->heapBuf) { free(dk->heapBuf); dk->heapBuf = NULL; } }

static void resetSrc(void) {
    dk->playing = false; dk->dropOn = false; dk->mixQ = 0;
    killGrains();                                        // nada puede leer el buffer que vamos a liberar
    freeHeap();
    dk->src = demoBuf; dk->srcLen = DEMO_LEN; dk->srcRate = DEMO_RATE;
    dk->lostSample = true;
}

static void useDemo(const char *name) {
    freeHeap();
    dk->src = demoBuf; dk->srcLen = DEMO_LEN; dk->srcRate = DEMO_RATE;
    dk->lostSample = false;
    strncpy(dk->curName, name, sizeof(dk->curName) - 1);
    computeAuto();
    updateInc();
    resetTransport(true, true);                  // demo: suena en loop de inmediato
    computePeaks();
}

// ---------------------------------------------------------------- WAV + cache
static void wr32(u8 *p, u32 v) { p[0] = (u8)v; p[1] = (u8)(v >> 8); p[2] = (u8)(v >> 16); p[3] = (u8)(v >> 24); }

// Cache: "<archivo>.wav.gr8" = cabecera de 16 bytes ('G','R','8',3, tamano del wav,
// frecuencia, largo) + muestras s8 ya normalizadas. Si el WAV cambia de tamano, se regenera.
static bool loadCache(const char *name, u32 wavSize) {
    char cn[160];
    snprintf(cn, sizeof(cn), "%s.gr8", name);
    FILE *f = fopen(cn, "rb");
    if (!f) return false;
    u8 h[16];
    if (fread(h, 1, 16, f) != 16 || h[0] != 'G' || h[1] != 'R' || h[2] != '8' || h[3] != 4 ||
        rd32(h + 4) != wavSize) { fclose(f); return false; }
    u32 rate = rd32(h + 8), len = rd32(h + 12);
    if (rate < 1000 || rate > 48000 || len < 256 || len > 1300000) { fclose(f); return false; }
    resetSrc();
    s8 *buf = (s8 *)malloc(len);
    if (!buf) { fclose(f); return false; }
    size_t got = 0;
    while (got < len) {                                  // por tandas: el otro deck sigue sonando
        size_t n = len - got;
        if (n > 2048) n = 2048;
        size_t r = fread(buf + got, 1, n, f);
        got += r;
        audioTick();
        if (r != n) break;
    }
    fclose(f);
    if (got != len) { free(buf); return false; }
    dk->heapBuf = buf; dk->src = buf; dk->srcLen = len; dk->srcRate = rate;
    dk->lostSample = false;
    strncpy(dk->curName, name, sizeof(dk->curName) - 1);
    computeAuto();
    updateInc();
    resetTransport(false, false);                // los tracks cargan en pausa, al inicio
    computePeaks();
    return true;
}

static void saveCache(const char *name, u32 wavSize, const s8 *buf, u32 len, u32 rate) {
    char cn[160];
    snprintf(cn, sizeof(cn), "%s.gr8", name);
    FILE *f = fopen(cn, "wb");
    if (!f) return;                                   // SD protegida o sin permisos: no pasa nada
    u8 h[16] = { 'G', 'R', '8', 4 };
    wr32(h + 4, wavSize); wr32(h + 8, rate); wr32(h + 12, len);
    bool ok = (fwrite(h, 1, 16, f) == 16);
    for (u32 o = 0; ok && o < len; ) {
        u32 n = len - o;
        if (n > 2048) n = 2048;
        audioTick();
        ok = (fwrite(buf + o, 1, n, f) == n);
        o += n;
    }
    fclose(f);
    if (!ok) remove(cn);
}

// mantener B durante una carga la cancela (asi la DS nunca parece colgada)
static bool loadCancelled(void) { scanKeys(); return (keysHeld() & KEY_B) != 0; }

// ---- canalizacion comun: mono s16 -> decimacion con promedio -> s8 normalizado
typedef struct { s8 *buf; u32 j, outLen, phase, cnt, rate, storeRate; s32 acc; int pk; } Pipe;

static s8 *pipeAlloc(Pipe *p, u32 frames, u32 rate) {
    u32 budget = BUDGET, storeRate, outLen;
    s8 *buf = NULL;
    while (1) {
        storeRate = rate;
        if (storeRate > 32728) storeRate = 32728;
        if ((u64)frames * storeRate / rate > budget)
            storeRate = (u32)((u64)budget * rate / frames);
        if (storeRate < 4000) storeRate = 4000;
        outLen = (u32)((u64)frames * storeRate / rate);
        buf = (s8 *)malloc(outLen);
        if (buf) break;
        budget = budget * 3 / 4;
        if (budget < 200000) return NULL;
    }
    p->buf = buf; p->j = 0; p->outLen = outLen; p->phase = 0; p->cnt = 0;
    p->rate = rate; p->storeRate = storeRate; p->acc = 0; p->pk = 0;
    return buf;
}

static inline void pipePush(Pipe *p, s32 m) {
    p->acc += m; p->cnt++;
    p->phase += p->storeRate;
    if (p->phase >= p->rate) {                      // decimacion con promedio (anti-alias basico)
        p->phase -= p->rate;
        if (p->j < p->outLen) {
            s8 v = (s8)((p->acc / (s32)p->cnt) >> 8);
            int av = v < 0 ? -v : v;
            if (av > p->pk) p->pk = av;
            p->buf[p->j++] = v;
        }
        p->acc = 0; p->cnt = 0;
    }
}

static const char *pipeFinish(Pipe *p, const char *name, u32 fileSize) {
    s8 *buf = p->buf;
    u32 j = p->j;
    if (j < 256) { free(buf); return "error leyendo la SD"; }
    if (p->pk > 0 && p->pk < 110) {                 // normaliza: sube samples bajitos hasta ~127
        s32 mul = (127 << 8) / p->pk;
        for (u32 i = 0; i < j; i++) {
            s32 v = ((s32)buf[i] * mul) >> 8;
            if (v > 127) v = 127;
            if (v < -127) v = -127;
            buf[i] = (s8)v;
        }
    }
    dk->heapBuf = buf; dk->src = buf; dk->srcLen = j; dk->srcRate = p->storeRate;
    dk->lostSample = false;
    strncpy(dk->curName, name, sizeof(dk->curName) - 1);
    computeAuto();
    updateInc();
    resetTransport(false, false);                   // los tracks cargan en pausa, al inicio
    computePeaks();
    drawLoadBar(100);
    drawLoadNote("guardando cache...");
    saveCache(name, fileSize, buf, j, p->storeRate);
    return NULL;
}

// ---- MP3: decodificador de punto fijo Helix (el ARM9 no tiene FPU)
#define MP3_IN 8192
static const char *loadMp3(FILE *f, const char *name, u32 fileSize) {
    u8 *ib = (u8 *)malloc(MP3_IN);
    s16 *pcm = (s16 *)malloc(MAX_NSAMP * MAX_NGRAN * MAX_NCHAN * sizeof(s16));
    HMP3Decoder dec = (ib && pcm) ? MP3InitDecoder() : NULL;
    if (!dec) { free(ib); free(pcm); fclose(f); return "sin memoria"; }
    const char *err = NULL;

    // salta la etiqueta ID3v2 si existe
    u32 dataStart = 0;
    if (fread(ib, 1, 10, f) == 10 && !memcmp(ib, "ID3", 3))
        dataStart = 10 + (((u32)ib[6] & 0x7F) << 21 | ((u32)ib[7] & 0x7F) << 14 | ((u32)ib[8] & 0x7F) << 7 | ((u32)ib[9] & 0x7F));
    fseek(f, (long)dataStart, SEEK_SET);

    // primer cuadro valido: frecuencia, canales y duracion estimada
    size_t have = fread(ib, 1, MP3_IN, f);
    int off = MP3FindSyncWord(ib, (int)have);
    MP3FrameInfo fi;
    if (off < 0 || MP3GetNextFrameInfo(dec, &fi, ib + off) != 0 || fi.layer != 3 || fi.samprate < 8000) {
        err = "no es un mp3 valido";
    }
    Pipe pp;
    u32 frames = 0;
    if (!err) {
        u32 spf = fi.version == MPEG1 ? 1152 : 576;
        u32 fr = 0;
        int xo = (fi.version == MPEG1 ? (fi.nChans == 2 ? 32 : 17) : (fi.nChans == 2 ? 17 : 9)) + 4;
        const u8 *x = ib + off + xo;                       // cabecera Xing/Info: cuenta exacta de cuadros (VBR)
        if ((size_t)off + (size_t)xo + 12 < have && (!memcmp(x, "Xing", 4) || !memcmp(x, "Info", 4)) && (x[7] & 1))
            fr = ((u32)x[8] << 24) | ((u32)x[9] << 16) | ((u32)x[10] << 8) | x[11];
        if (fr) frames = fr * spf;
        else if (fi.bitrate > 0)                           // CBR: tamano / bitrate
            frames = (u32)((u64)(fileSize - dataStart) * 8 * (u64)fi.samprate / (u32)fi.bitrate);
        if (frames > (u32)MAX_SECS * (u32)fi.samprate) frames = (u32)MAX_SECS * (u32)fi.samprate;
        if (frames < 2048) err = "archivo muy corto";
    }
    if (!err) {
        resetSrc();
        if (!pipeAlloc(&pp, frames, (u32)fi.samprate)) err = "sin memoria";
    }
    if (err) { MP3FreeDecoder(dec); free(ib); free(pcm); fclose(f); return err; }

    u32 done = 0, bad = 0, nb = 0, outSamps = 0;
    bool cancelled = false;
    bool eof = (have < MP3_IN);
    while (done < frames && bad < 400) {
        if (have < 3000 && !eof) {                         // rellena el buffer de entrada
            size_t got = fread(ib + have, 1, MP3_IN - have, f);
            have += got;
            if (got == 0) eof = true;
        }
        int o = MP3FindSyncWord(ib, (int)have);
        if (o < 0) { have = 0; if (eof) break; continue; }
        if (o > 0) { memmove(ib, ib + o, have - (size_t)o); have -= (size_t)o; }
        const u8 *p = ib;
        size_t left = have;
        int r = MP3Decode(dec, &p, &left, pcm, 0);
        size_t used = (size_t)(p - ib);
        if (r == ERR_MP3_NONE) {
            MP3FrameInfo li;
            MP3GetLastFrameInfo(dec, &li);
            int nc = li.nChans ? li.nChans : 1;
            u32 ns = (u32)li.outputSamps / (u32)nc;
            for (u32 i = 0; i < ns && done < frames; i++, done++)
                pipePush(&pp, nc == 2 ? ((s32)pcm[2 * i] + (s32)pcm[2 * i + 1]) >> 1 : (s32)pcm[i]);
            outSamps += ns;
            bad = 0;
        } else if (r == ERR_MP3_INDATA_UNDERFLOW || r == ERR_MP3_MAINDATA_UNDERFLOW) {
            if (used == 0) used = 1;                       // evita quedarnos pegados
            if (eof && have < 1500) break;
            bad++;
        } else {
            if (used == 0) used = 1;                       // cuadro danado: salta un byte y resincroniza
            bad++;
        }
        if (used > have) used = have;
        memmove(ib, ib + used, have - used);
        have -= used;
        if (have == 0 && eof) break;
        audioTick();
        if ((++nb & 7) == 0) {
            drawLoadBar((int)(done / (frames / 100 + 1)));
            if (loadCancelled()) { cancelled = true; break; }
        }
    }
    (void)outSamps;
    MP3FreeDecoder(dec);
    free(ib); free(pcm);
    fclose(f);
    if (cancelled) { free(pp.buf); return "cancelado"; }
    return pipeFinish(&pp, name, fileSize);
}

// devuelve NULL si todo bien, o un mensaje de error
static const char *loadWav(const char *name) {
    FILE *f = fopen(name, "rb");
    if (!f) return "no se pudo abrir";

    fseek(f, 0, SEEK_END);
    u32 wavSize = (u32)ftell(f);
    fseek(f, 0, SEEK_SET);
    if (loadCache(name, wavSize)) { fclose(f); return NULL; }   // ya convertido antes
    {
        size_t nl = strlen(name);
        if (nl > 4 && !strcasecmp(name + nl - 4, ".mp3")) return loadMp3(f, name, wavSize);
    }

    u8 h[12];
    if (fread(h, 1, 12, f) != 12 || memcmp(h, "RIFF", 4) || memcmp(h + 8, "WAVE", 4)) {
        fclose(f); return "no es un WAV";
    }

    u16 fmt = 0, ch = 0, bits = 0;
    u32 rate = 0, dataLen = 0;
    bool haveFmt = false, haveData = false;
    u8 c[8];
    while (fread(c, 1, 8, f) == 8) {
        u32 sz = rd32(c + 4);
        if (!memcmp(c, "fmt ", 4)) {
            u8 b[16];
            if (sz < 16 || fread(b, 1, 16, f) != 16) { fclose(f); return "fmt invalido"; }
            fmt = rd16(b); ch = rd16(b + 2); rate = rd32(b + 4); bits = rd16(b + 14);
            haveFmt = true;
            fseek(f, (long)(sz - 16 + (sz & 1)), SEEK_CUR);
        } else if (!memcmp(c, "data", 4)) {
            dataLen = sz; haveData = true; break;
        } else {
            fseek(f, (long)(sz + (sz & 1)), SEEK_CUR);
        }
    }
    if (!haveFmt || !haveData) { fclose(f); return "WAV incompleto"; }
    if ((fmt != 1 && fmt != 0xFFFE) || (ch != 1 && ch != 2) ||
        (bits != 8 && bits != 16 && bits != 24) || rate == 0) {
        fclose(f); return "solo PCM 8/16/24 mono/estereo";
    }

    long pos = ftell(f);
    fseek(f, 0, SEEK_END);
    long end = ftell(f);
    fseek(f, pos, SEEK_SET);
    if ((long)dataLen > end - pos) dataLen = (u32)(end - pos);   // WAV en streaming o truncado

    u32 blockAlign = (u32)ch * (bits / 8);
    u32 frames = dataLen / blockAlign;
    if (frames > (u32)MAX_SECS * rate) frames = (u32)MAX_SECS * rate;   // max 2 min
    if (frames < 256) { fclose(f); return "archivo muy corto"; }

    // liberamos el sample anterior antes de pedir RAM; si falla volvemos al demo
    resetSrc();

    Pipe pp;
    if (!pipeAlloc(&pp, frames, rate)) { fclose(f); return "sin memoria"; }
    u8 *blk = (u8 *)malloc(4096);
    if (!blk) { free(pp.buf); fclose(f); return "sin memoria"; }
    u32 perBlk = 4096 / blockAlign, done = 0, nb = 0;
    while (done < frames) {
        u32 n = frames - done;
        if (n > perBlk) n = perBlk;
        if (fread(blk, blockAlign, n, f) != n) break;
        for (u32 k = 0; k < n; k++) {
            const u8 *p = blk + k * blockAlign;
            s32 m;
            if (bits == 16) {
                m = (s16)rd16(p);
                if (ch == 2) m = (m + (s16)rd16(p + 2)) >> 1;
            } else if (bits == 8) {
                m = ((s32)p[0] - 128) * 256;
                if (ch == 2) m = (m + ((s32)p[1] - 128) * 256) >> 1;
            } else {
                m = (s16)rd16(p + 1);                       // 24 bit: nos quedamos con los 16 altos
                if (ch == 2) m = (m + (s16)rd16(p + 4)) >> 1;
            }
            pipePush(&pp, m);
        }
        done += n;
        audioTick();
        if ((++nb & 31) == 0) drawLoadBar((int)(done / (frames / 100 + 1)));
        if ((nb & 7) == 0 && loadCancelled()) { free(blk); free(pp.buf); fclose(f); return "cancelado"; }
    }
    free(blk);
    fclose(f);
    return pipeFinish(&pp, name, wavSize);
}

// ---------------------------------------------------------------- navegador
#define MAX_ENT 128
typedef struct { char name[128]; u8 dir; } Ent;
static Ent ents[MAX_ENT];
static int nEnt = 0, sel = 0, scrollTop = 0;

static int entCmp(const void *a, const void *b) {
    const Ent *x = (const Ent *)a, *y = (const Ent *)b;
    if (x->dir != y->dir) return (int)y->dir - (int)x->dir;   // carpetas primero
    return strcasecmp(x->name, y->name);
}

static void scanDir(void) {
    nEnt = 0; sel = 0; scrollTop = 0;
    DIR *d = opendir(".");
    if (!d) return;
    struct dirent *e;
    while ((e = readdir(d)) && nEnt < MAX_ENT) {
        if (!strcmp(e->d_name, ".")) continue;
        bool dir = (e->d_type == DT_DIR);
        if (!dir) {
            size_t n = strlen(e->d_name);
            if (n < 5 || (strcasecmp(e->d_name + n - 4, ".wav") && strcasecmp(e->d_name + n - 4, ".mp3"))) continue;
        }
        strncpy(ents[nEnt].name, e->d_name, sizeof(ents[nEnt].name) - 1);
        ents[nEnt].name[sizeof(ents[nEnt].name) - 1] = 0;
        ents[nEnt].dir = dir;
        nEnt++;
    }
    closedir(d);
    qsort(ents, nEnt, sizeof(Ent), entCmp);
}

#define BR_ROWS 14

static void drawBrowser(void) {
    clearScreen(fbTop, C_BG);
    char cwd[256], t[40];
    if (!getcwd(cwd, sizeof(cwd))) strcpy(cwd, "?");
    snprintf(t, sizeof t, "%.34s", cwd);
    drawHeader("SD", t, C_ORG);
    if (nEnt == 0) text(fbTop, 8, 24, "(sin .mp3/.wav ni carpetas)", C_GRAY, 1);
    for (int r = 0; r < BR_ROWS; r++) {
        int i = scrollTop + r;
        if (i >= nEnt) break;
        int y = 21 + r * 11;
        bool sl = (i == sel);
        if (sl) rect(fbTop, 0, y, VW - 8, 11, C_YEL);
        char n[40];
        if (ents[i].dir) snprintf(n, sizeof n, "[%.34s]", ents[i].name);
        else             snprintf(n, sizeof n, "%.36s", ents[i].name);
        text(fbTop, 8, y + 1, n, sl ? C_DARK : (ents[i].dir ? C_ORG : C_LGRAY), 1);
    }
    if (nEnt > BR_ROWS) {                                    // barra de scroll
        int full = BR_ROWS * 11;
        int th = full * BR_ROWS / nEnt;
        if (th < 6) th = 6;
        int ty = 21 + (full - th) * scrollTop / (nEnt - BR_ROWS);
        rect(fbTop, 250, 21, 3, full, C_PANEL2);
        rect(fbTop, 250, ty, 3, th, C_ORG);
    }
    int x = 8;
    keyHint(&x, 178, "A", "abrir");
    keyHint(&x, 178, "B", "volver");
}

// abre el navegador de la SD (desde el menu o el boton de carpeta)
static void openBrowser(void) {
    if (!sdOK) return;
    touching = false; touchDrag = false; freezeKey = false;
    scanDir();
    browsing = true;
    drawBrowser();
}

// ---------------------------------------------------------------- parametros / texto
enum { P_SPEED, P_PITCH, P_SIZE, P_DENS, P_SPRAY, P_DRIFT, P_HARM, P_SHIM, P_JIT, P_REV,
       P_REVERB, P_DLY, P_FLUT, P_FILT, P_SWEEP, P_VOL, P_COUNT };
static const char *const pLabel[P_COUNT] = {
    "VELOCID", "PITCH", "TAMANO", "DENSID", "SPRAY", "DERIVA", "ARMONIA", "SHIMMER", "JITTER", "REVERSA",
    "REVERB", "TAPE DLY", "FLUTTER", "FILTRO", "BARRIDO", "VOLUMEN"
};
static int cur = 0;

static s32 stepSize(s32 v) { return v < 100 ? 10 : (v < 500 ? 50 : 100); }

static void adjust(int d) {
    switch (cur) {
        case P_SPEED: dk->speedPct = clampi(dk->speedPct + d * 5, -200, 200); updateInc(); break;
        case P_PITCH: dk->semis    = clampi(dk->semis + d, -24, 24);          updateInc(); break;
        case P_SIZE:  sizeMs   = clampi(sizeMs + d * stepSize(d > 0 ? sizeMs : sizeMs - 1), 10, 2000); updateInc(); break;
        case P_DENS:  density  = clampi(density + d * ((d > 0 ? density : density - 1) < 10 ? 1 : 2), 1, 100); updateInc(); break;
        case P_SPRAY: sprayMs  = clampi(sprayMs + d * 10, 0, 500);    break;
        case P_DRIFT: driftPct = clampi(driftPct + d * 5, 0, 100);    if (!driftPct) dk->driftW = 0; break;
        case P_HARM:  harmPct  = clampi(harmPct + d * 5, 0, 100);     break;
        case P_SHIM:  shimPct  = clampi(shimPct + d * 5, 0, 100);     break;
        case P_DLY:   delayPct = clampi(delayPct + d * 5, 0, 100);    updateDelay(); break;
        case P_FLUT:  flutPct  = clampi(flutPct + d * 5, 0, 100);     updateFlutter(); break;
        case P_FILT:  filtPct  = clampi(filtPct + d * 4, 0, 100);     break;
        case P_SWEEP: sweepPct = clampi(sweepPct + d * 5, 0, 100);    break;
        case P_JIT:   jitterC  = clampi(jitterC + d * 5, 0, 100);     break;
        case P_REV:   revPct   = clampi(revPct + d * 10, 0, 100);     break;
        case P_REVERB: revMixPct = clampi(revMixPct + d * 5, 0, 100); updateReverb(); break;
        case P_VOL:   gain     = clampi(gain + d * 8, 8, 240);        updateInc(); break;
        default: break;
    }
}

static void valStr(int i, char *b, size_t n) {
    s32 tg = gain * 10 / 40;                              // 40 = 1.0x
    switch (i) {
        case P_SPEED: snprintf(b, n, "%c %+ld%%", 'A' + actDeck, (long)dk->speedPct); break;
        case P_PITCH: snprintf(b, n, "%c %+ld st", 'A' + actDeck, (long)dk->semis); break;
        case P_SIZE:  snprintf(b, n, "%ld ms", (long)sizeMs); break;
        case P_DENS:  snprintf(b, n, "%ld /s", (long)density); break;
        case P_SPRAY: snprintf(b, n, "%ld ms", (long)sprayMs); break;
        case P_DRIFT: snprintf(b, n, "%ld%%", (long)driftPct); break;
        case P_HARM:  snprintf(b, n, "%ld%%", (long)harmPct); break;
        case P_SHIM:  snprintf(b, n, "%ld%%", (long)shimPct); break;
        case P_DLY:   snprintf(b, n, "%ld%%", (long)delayPct); break;
        case P_FLUT:  snprintf(b, n, "%ld%%", (long)flutPct); break;
        case P_FILT:
            if (filtPct >= 100) snprintf(b, n, "abierto");
            else                snprintf(b, n, "%ld Hz", (long)fcHz[filtPct * 127 / 100]);
            break;
        case P_SWEEP:
            if (sweepPct) snprintf(b, n, "%ld%%", (long)sweepPct);
            else          snprintf(b, n, "off");
            break;
        case P_JIT:   snprintf(b, n, "%ld cent", (long)jitterC); break;
        case P_REV:   snprintf(b, n, "%ld%%", (long)revPct); break;
        case P_REVERB: snprintf(b, n, "%ld%%", (long)revMixPct); break;
        case P_VOL:   snprintf(b, n, "%ld.%ld x", (long)(tg / 10), (long)(tg % 10)); break;
        default:      b[0] = 0; break;
    }
}

static void fmtT(char *b, size_t n, u32 tenths) {
    snprintf(b, n, "%lu:%02lu.%lu", (unsigned long)(tenths / 600),
             (unsigned long)((tenths / 10) % 60), (unsigned long)(tenths % 10));
}

// 0..256 para la barra de cada parametro (-1 = sin barra)
static s32 paramFrac(int i) {
    switch (i) {
        case P_SPEED:  return (dk->speedPct + 200) * 256 / 400;
        case P_PITCH:  return (dk->semis + 24) * 256 / 48;
        case P_SIZE:   return isqrt32((u32)sizeMs * 65536u / 2000u);
        case P_DENS:   return density * 256 / 100;
        case P_SPRAY:  return sprayMs * 256 / 500;
        case P_DRIFT:  return driftPct * 256 / 100;
        case P_HARM:   return harmPct * 256 / 100;
        case P_SHIM:   return shimPct * 256 / 100;
        case P_DLY:    return delayPct * 256 / 100;
        case P_FLUT:   return flutPct * 256 / 100;
        case P_FILT:   return filtPct * 256 / 100;
        case P_SWEEP:  return sweepPct * 256 / 100;
        case P_JIT:    return jitterC * 256 / 100;
        case P_REV:    return revPct * 256 / 100;
        case P_REVERB: return revMixPct * 256 / 100;
        case P_VOL:    return gain * 256 / 240;
        default:       return -1;
    }
}

static char sigCache[20][128];
static bool topFull = true;

// true si lo que va en ese bloque cambio desde la ultima vez (asi solo se redibuja lo necesario)
static bool sigChanged(int slot, const char *sig) {
    if (!topFull && !strcmp(sigCache[slot], sig)) return false;
    strncpy(sigCache[slot], sig, sizeof(sigCache[slot]) - 1);
    sigCache[slot][sizeof(sigCache[slot]) - 1] = 0;
    return true;
}

// ---- dibujo de cinta: lineas, discos, carretes
static void putpx(u16 *s, int x, int y, u16 c) { if ((unsigned)x < VW && (unsigned)y < VH) s[y * VW + x] = c; }

static void line(u16 *s, int x0, int y0, int x1, int y1, u16 c) {
    int dx = x1 > x0 ? x1 - x0 : x0 - x1, dy = y1 > y0 ? y0 - y1 : y1 - y0;
    int sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1, err = dx + dy;
    for (int n = 0; n < 200; n++) {
        putpx(s, x0, y0, c);
        if (x0 == x1 && y0 == y1) break;
        int e2 = 2 * err;
        if (e2 >= dy) { err += dy; x0 += sx; }
        if (e2 <= dx) { err += dx; y0 += sy; }
    }
}

static void disc(u16 *s, int cx, int cy, int r, u16 c) {
    for (int dy = -r; dy <= r; dy++) {
        int w = isqrt32((u32)(r * r - dy * dy) + (u32)r / 2);
        rect(s, cx - w, cy + dy, 2 * w + 1, 1, c);
    }
}

static void ringO(u16 *s, int cx, int cy, int r, u16 c) {
    for (int dy = -r; dy <= r; dy++) {
        int w = isqrt32((u32)(r * r - dy * dy) + (u32)r / 2);
        putpx(s, cx - w, cy + dy, c); putpx(s, cx + w, cy + dy, c);
        if (dy == -r || dy == r) rect(s, cx - w, cy + dy, 2 * w + 1, 1, c);
    }
}

// un carrete: paquete de cinta (radio rp), pestana, nucleo y 3 radios que giran
static void drawReel(int cx, int cy, int rp, int ang64, u16 hub) {
    disc(fbTop, cx, cy, rp, C_YELD);
    ringO(fbTop, cx, cy, 10, C_LGRAY);
    ringO(fbTop, cx, cy, rp, C_ORGD);
    for (int k = 0; k < 3; k++) {
        int a = (ang64 + k * 21 + (k + 1) / 2) & 63;               // 0, 21, 43 ~ tercios de 64
        int ca = sinT[(a + 16) & 63], sa = sinT[a];
        line(fbTop, cx + (ca * 3 >> 8), cy + (sa * 3 >> 8), cx + (ca * 8 >> 8), cy + (sa * 8 >> 8), C_DARK);
    }
    disc(fbTop, cx, cy, 3, hub);
    putpx(fbTop, cx, cy, C_DARK);
}

static s32 heardPosD(Deck *d, u32 ahead);

// ---------------------------------------------------------------- vista de knobs
// Se dibuja siempre en el motor principal (fbTop). Con "PANTALLAS" las dos pantallas se
// intercambian fisicamente y esta vista queda abajo, donde se toca.
#define PNL_Y   15                  // paneles de deck
#define PNL_H   38
#define KY0     58                  // rejilla de knobs: 4 columnas x 2 filas
#define KCH     50
#define TAB_Y   160

#define NPAGES 2
static const s8 pageKn[NPAGES][8] = {
    { P_SPEED, P_PITCH, P_VOL, P_FLUT, P_REVERB, P_DLY, P_FILT, P_SWEEP },     // mezcla + espacio juntos
    { P_SIZE, P_DENS, P_SPRAY, P_DRIFT, P_HARM, P_SHIM, P_JIT, P_REV }
};
static const char *const pageName[NPAGES] = { "MEZCLA", "NUBE" };
static int kPage = 0, kSel = 0;
static bool swapped = false;        // false: knobs arriba, ondas abajo (tactil). true: al reves.

static int knobAt(int page, int k) { return (k >= 0 && k < 8) ? pageKn[page][k] : -1; }
static void selectKnob(int k) { if (knobAt(kPage, k) >= 0) { kSel = k; cur = pageKn[kPage][k]; } }
static void setPage(int p) {
    kPage = (p + NPAGES) % NPAGES;
    if (knobAt(kPage, kSel) < 0) kSel = 0;
    cur = pageKn[kPage][kSel];
}
static void moveKnob(int dir) {
    for (int n = 0; n < 8; n++) {
        kSel = (kSel + dir + 8) & 7;
        if (knobAt(kPage, kSel) >= 0) break;
    }
    cur = pageKn[kPage][kSel];
}

#ifndef LCD_SWAP_REG
#define LCD_SWAP_REG (*(volatile u16 *)0x04000304)       // REG_POWERCNT: el bit 15 intercambia las pantallas
#endif
static void doSwap(void) { swapped = !swapped; LCD_SWAP_REG ^= (u16)(1 << 15); }

static void drawDeckPanel(int di, s32 heard, bool statics) {
    Deck *d = &decks[di];
    int px = di ? 129 : 1;
    bool act = (di == actDeck);
    char sig[64];
    if (statics) {
        rect(fbTop, px, PNL_Y, 126, PNL_H, C_PANEL);
        u16 bc = act ? C_ORG : C_LINE;
        rect(fbTop, px, PNL_Y, 126, 1, bc); rect(fbTop, px, PNL_Y + PNL_H - 1, 126, 1, bc);
        rect(fbTop, px, PNL_Y, 1, PNL_H, bc); rect(fbTop, px + 125, PNL_Y, 1, PNL_H, bc);
        pill(fbTop, px + 4, PNL_Y + 3, 13, 9, act ? C_ORG : C_PANEL2);
        text(fbTop, px + 7, PNL_Y + 3, di ? "B" : "A", act ? C_DARK : C_LGRAY, 1);
        char nm[24];
        snprintf(nm, sizeof nm, "%.11s", d->curName);
        text(fbTop, px + 20, PNL_Y + 3, nm, act ? C_WHITE : C_LGRAY, 1);
        sigCache[1 + di][0] = 0; sigCache[3 + di][0] = 0;       // fuerza el redibujo de lo de adentro
    }
    // carretes: el paquete de cinta pasa de un carrete al otro segun la posicion
    u32 len = d->srcLen ? d->srcLen : 1;
    s32 fr = (s32)((u32)(d->posI < 0 ? 0 : d->posI) * 255 / len);
    int rl = 4 + (255 - fr) * 5 / 255, rr = 4 + fr * 5 / 255;
    if (d->playing) d->reel += 3 << 10;
    int ang = (int)((u32)d->reel >> 10) & 63;
    snprintf(sig, sizeof sig, "%d|%d|%d|%d", ang, rl, rr, (int)d->playing);
    if (sigChanged(1 + di, sig)) {
        int cxl = px + 17, cxr = px + 47, cy = PNL_Y + 24;
        rect(fbTop, px + 2, PNL_Y + 14, 60, 23, C_PANEL);
        line(fbTop, cxl, cy + rl, cxr, cy + rr, C_YELD);                       // cinta entre carretes
        drawReel(cxl, cy, rl, ang, C_GRAY);
        drawReel(cxr, cy, rr, (ang + 9) & 63, C_GRAY);
        rect(fbTop, px + 27, cy + 7, 10, 3, d->playing ? C_ORG : C_GRAY);       // cabezal
    }

    // contador + estado
    char a[20], b[20];
    u32 now10 = (u32)heard * 10 / d->srcRate, len10 = d->srcLen * 10 / d->srcRate;
    fmtT(a, sizeof a, now10); fmtT(b, sizeof b, len10);
    int stt = (act && loopEdit) ? 1 : 0;
    int isLoop = (d->loopStart > 0 || d->loopEnd < (s32)d->srcLen - 1);
    snprintf(sig, sizeof sig, "%s|%s|%d|%d|%d", a, b, stt, (int)d->playing, isLoop);
    if (sigChanged(3 + di, sig)) {
        rect(fbTop, px + 64, PNL_Y + 14, 60, 23, C_PANEL);
        text(fbTop, px + 66, PNL_Y + 16, a, C_YEL, 1);
        char t2[24];
        snprintf(t2, sizeof t2, "/%s", b);
        text(fbTop, px + 66, PNL_Y + 26, t2, C_GRAY, 1);
        rect(fbTop, px + 73, PNL_Y + 2, 51, 11, C_PANEL);
        int x = px + 121;
        if (!d->playing) { x -= textW("||", 1); text(fbTop, x, PNL_Y + 3, "||", C_ORG, 1); x -= 5; }
        if (stt)         { x -= textW("EDIT", 1); text(fbTop, x, PNL_Y + 3, "EDIT", C_WHITE, 1); }
        else if (isLoop) { x -= textW("LOOP", 1); text(fbTop, x, PNL_Y + 3, "LOOP", C_YEL, 1); }
    }
}

static void drawKnob(int k, int pid, bool sel) {
    int col = k & 3, row = k >> 2;
    int x0 = col * 64 + 1, y0 = KY0 + row * KCH, cx = col * 64 + 32, cy = y0 + 25;
    rect(fbTop, x0, y0, 62, KCH - 2, sel ? C_PANEL : C_BG);
    if (pid < 0) return;
    const char *lb = pLabel[pid];
    text(fbTop, cx - textW(lb, 1) / 2, y0 + 1, lb, sel ? C_YEL : C_GRAY, 1);
    s32 f = paramFrac(pid);
    if (f < 0) f = 0;
    if (f > 256) f = 256;
    int lit = (int)((f * 10 + 128) / 256);                      // cuantos puntos del aro estan encendidos
    for (int t = 0; t <= 10; t++) {
        int a = 24 + t * 48 / 10;
        int tx = cx + ((sinT[(a + 16) & 63] * 15) >> 8), ty = cy + ((sinT[a & 63] * 15) >> 8);
        rect(fbTop, tx - 1, ty - 1, 2, 2, t <= lit && f > 0 ? C_ORG : C_PANEL2);
    }
    disc(fbTop, cx, cy, 10, sel ? C_LINE : C_PANEL2);
    int a = 24 + (int)(f * 48 / 256);
    int ca = sinT[(a + 16) & 63], sa = sinT[a & 63];
    line(fbTop, cx + (ca * 3 >> 8), cy + (sa * 3 >> 8), cx + (ca * 9 >> 8), cy + (sa * 9 >> 8), C_WHITE);
    char v[24];
    valStr(pid, v, sizeof v);
    text(fbTop, cx - textW(v, 1) / 2, y0 + 37, v, sel ? C_WHITE : C_LGRAY, 1);
}

static void drawTabs(void) {
    rect(fbTop, 0, TAB_Y - 2, VW, VH - TAB_Y + 2, C_BG);
    for (int p = 0; p < NPAGES; p++) {
        int x = 4 + p * 88;
        bool on = (p == kPage);
        pill(fbTop, x, TAB_Y + 2, 84, 24, on ? C_ORG : C_PANEL2);
        text(fbTop, x + 42 - textW(pageName[p], 1) / 2, TAB_Y + 9, pageName[p], on ? C_DARK : C_LGRAY, 1);
    }
    pill(fbTop, 182, TAB_Y + 2, 70, 24, C_PANEL2);
    text(fbTop, 217 - textW("PANTALLAS", 1) / 2, TAB_Y + 9, "PANTALLAS", C_LGRAY, 1);
}

static void drawKView(u32 lead) {
    if (topFull) clearScreen(fbTop, C_BG);
    char sig[128];

    snprintf(sig, sizeof sig, "%d|%d|%d", (int)sdOK, (int)xfade, (int)grainCap);
    if (sigChanged(0, sig)) {
        rect(fbTop, 0, 0, VW, 14, C_PANEL);
        rect(fbTop, 0, 0, 4, 14, C_ORG);
        text(fbTop, 10, 2, "EFEES", C_WHITE, 1);
        text(fbTop, 46, 2, "reel to reel", C_ORG, 1);
        if (!sdOK) text(fbTop, 126, 2, "sin SD", C_GRAY, 1);
        else if (grainCap < 8) { char gs[12]; snprintf(gs, sizeof gs, "g%d", (int)grainCap); text(fbTop, 130, 2, gs, C_GRAY, 1); }
        char x[16];
        snprintf(x, sizeof x, "A %ld%% B", (long)(xfade * 100 / 256));
        text(fbTop, VW - 6 - textW(x, 1), 2, x, C_YEL, 1);
    }

    for (int di = 0; di < 2; di++) {
        bool st = topFull;
        snprintf(sig, sizeof sig, "%d|%d|%.100s", di == actDeck, di, decks[di].curName);
        if (sigChanged(16 + di, sig)) st = true;
        drawDeckPanel(di, heardPosD(&decks[di], lead), st);
        audioTick();
    }

    snprintf(sig, sizeof sig, "%d", (int)xfade);               // nivel de cada deck segun el crossfader
    if (sigChanged(13, sig)) {
        rect(fbTop, 1, 54, 126, 2, C_BG);  rect(fbTop, 129, 54, 126, 2, C_BG);
        rect(fbTop, 1, 54, 126 * xfGainA / 256, 2, C_ORG);
        rect(fbTop, 129, 54, 126 * xfGainB / 256, 2, C_ORG);
    }

    for (int k = 0; k < 8; k++) {
        int pid = knobAt(kPage, k);
        char v[24];
        if (pid >= 0) valStr(pid, v, sizeof v); else v[0] = 0;
        snprintf(sig, sizeof sig, "%d|%d|%d|%s|%c", pid, (int)(pid >= 0 && k == kSel), pid >= 0 ? (int)paramFrac(pid) : 0, v, 'A' + actDeck);
        if (sigChanged(5 + k, sig)) drawKnob(k, pid, pid >= 0 && k == kSel);
    }
    audioTick();

    snprintf(sig, sizeof sig, "%d", kPage);
    if (sigChanged(14, sig)) drawTabs();
    topFull = false;
}

// ---------------------------------------------------------------- vista (pantalla tactil)
// Cada deck es una columna vertical: el tiempo corre de arriba hacia abajo y la cabeza es una
// linea horizontal (como la cinta pasando por el cabezal).
#define TOPY    12                   // filas reservadas arriba para la etiqueta del deck
#define PH      118                  // filas de la onda (tiempo)
#define WAVE_H  (TOPY + PH)          // 130
#define XF_Y    132                  // crossfader
#define BAR_Y   156
#define COLW    50                   // medio ancho de cada columna
#define AMPX    46
static const int colX[2] = { 58, 198 };

#define C_SPRAY    RGB8( 46,  46,  52)
#define C_LOOPBG   RGB8( 58,  40,  50)
#define C_LOOPSPR  RGB8( 74,  50,  64)
#define C_AXIS     RGB8( 52,  52,  58)

typedef struct { int cy, spr, gh, ls, le; bool lon, drop; } View;
static View lastV[2];
static bool lastPlaying = false, lastLoopOn = false, lastDrop = false;
static int lastAct = -1;
static s32 lastXf = -1;

static void computePeaks(void) {
    for (int r = 0; r < PH; r++) {
        u32 i0 = dk->srcLen * (u32)r / PH;
        u32 i1 = dk->srcLen * (u32)(r + 1) / PH;
        if (i1 <= i0) i1 = i0 + 1;
        u32 step = (i1 - i0) / 64;                   // maximo ~64 puntos por fila
        if (step < 1) step = 1;
        int mn = 127, mx = -127;
        for (u32 i = i0; i < i1 && i < dk->srcLen; i += step) {
            int v = dk->src[i];
            if (v < mn) mn = v;
            if (v > mx) mx = v;
        }
        if (mn > mx) mn = mx = 0;
        dk->pkA[r] = (u8)(64 + mn * AMPX / 127);
        dk->pkB[r] = (u8)(64 + mx * AMPX / 127);
    }
    fullRedraw = true;
}

static View viewOf(Deck *d, s32 heardI) {
    View v;
    u32 len = d->srcLen;
    v.cy = (int)((u32)heardI * PH / len);
    if (v.cy > PH - 1) v.cy = PH - 1;
    v.spr = (int)((u32)(sprayMs * d->srcRate / 1000) * PH / len);
    v.gh  = (int)((u32)(sizeMs * d->srcRate / 1000) * PH / len);
    if (v.gh < 1) v.gh = 1;
    v.ls  = (int)((u32)d->loopStart * PH / len);
    v.le  = (int)((u32)d->loopEnd * PH / len);
    v.lon = d->loopStart > 0 || d->loopEnd < (s32)d->srcLen - 1;   // tinte solo si el loop no es todo el track
    v.drop = d->dropOn;
    return v;
}

static void drawRow(int di, int r, const View *v) {
    Deck *d = &decks[di];
    int cx = colX[di], x0 = cx - COLW, y = TOPY + r;
    if (r == v->cy) { rect(fb, x0, y, 2 * COLW + 1, 1, v->drop ? C_WHITE : C_ORG); return; }
    bool inLoop  = v->lon && r >= v->ls && r <= v->le;
    bool inSpray = r >= v->cy - v->spr && r <= v->cy + v->spr;
    u16 bg = inLoop ? (inSpray ? C_LOOPSPR : C_LOOPBG) : (inSpray ? C_SPRAY : C_BG);
    if (v->lon && (r == v->ls || r == v->le)) bg = C_YEL;
    // gris = por tocar, amarillo claro = ya sonado, blanco = ancho de un grano
    u16 wv = (r >= v->cy && r < v->cy + v->gh) ? C_WHITE : (r < v->cy ? C_YEL : C_GRAY);
    rect(fb, x0, y, 2 * COLW + 1, 1, bg);
    putpx(fb, cx, y, C_AXIS);
    int a = d->pkA[r] - 64, b = d->pkB[r] - 64;
    rect(fb, cx + a, y, b - a + 1, 1, wv);
}

static void drawRows(int di, int r0, int r1, const View *v) {
    if (r0 < 0) r0 = 0;
    if (r1 > PH - 1) r1 = PH - 1;
    for (int r = r0; r <= r1; r++) drawRow(di, r, v);
}

static void drawTags(void) {                                // etiquetas A / B arriba de cada columna
    for (int di = 0; di < 2; di++) {
        bool act = (di == actDeck);
        int x = colX[di] - COLW;
        rect(fb, x, 0, 2 * COLW + 1, TOPY - 1, C_BG);
        pill(fb, x, 1, 15, 10, act ? C_ORG : C_PANEL2);
        text(fb, x + 4, 1, di ? "B" : "A", act ? C_DARK : C_LGRAY, 1);
        char nm[16];
        snprintf(nm, sizeof nm, "%.13s", decks[di].curName);
        text(fb, x + 19, 1, nm, act ? C_WHITE : C_GRAY, 1);
    }
}

static void drawGrains(void) {                              // marcas de granos al lado de cada columna
    for (int di = 0; di < 2; di++) {
        Deck *d = &decks[di];
        int tx = di ? colX[di] - COLW - 7 : colX[di] + COLW + 3;
        rect(fb, tx, TOPY, 4, PH, C_BG);
        for (int g = 0; g < MAX_GRAINS; g++) {
            if (!d->grains[g].on || d->grains[g].ipos >= d->srcLen) continue;
            int gy = (int)(d->grains[g].ipos * PH / d->srcLen);
            rect(fb, tx, TOPY + gy, 4, 1, C_YEL);
        }
    }
}

static void drawXfade(void) {
    rect(fb, 0, WAVE_H, VW, BAR_Y - WAVE_H, C_PANEL);
    rect(fb, 0, WAVE_H, VW, 1, C_LINE);
    text(fb, 6, XF_Y + 6, "A", xfade < 128 ? C_YEL : C_GRAY, 1);
    text(fb, 244, XF_Y + 6, "B", xfade >= 128 ? C_YEL : C_GRAY, 1);
    rect(fb, 20, XF_Y + 10, 216, 3, C_PANEL2);
    for (int k = 0; k <= 4; k++) rect(fb, 20 + k * 54, XF_Y + 6, 1, 11, C_LINE);
    int kx = 20 + xfade * 216 / 256;
    rect(fb, kx - 5, XF_Y + 3, 11, 17, C_ORG);
    rect(fb, kx, XF_Y + 3, 1, 17, C_DARK);
    lastXf = xfade;
}

// triangulo relleno apuntando a la derecha (dir=+1) o a la izquierda (dir=-1), 14 filas
static void fillTri(int x, int y, int dir, u16 c) {
    for (int r = 0; r < 14; r++) {
        int w = (r < 7 ? r + 1 : 14 - r) * 2;
        if (dir > 0) rect(fb, x, y + r, w, 1, c);
        else         rect(fb, x - w, y + r, w, 1, c);
    }
}

#define BTN_Y  159
#define BTN_H  30
#define BTN_W  38

static void btnFrame(int x, u16 bg) { pill(fb, x, BTN_Y, BTN_W, BTN_H, bg); }
static void btnLabel(int x, const char *t, u16 c) { text(fb, x + (BTN_W - textW(t, 1)) / 2, 177, t, c, 1); }

// 6 botones de 38 px, paso 42: x = 4, 46, 88, 130, 172, 214. Cortes del toque en main: 44, 86, 128, 170, 212.
// Todos actuan sobre el deck activo.
static void drawButtons(void) {
    rect(fb, 0, BAR_Y, VW, VH - BAR_Y, C_PANEL);
    int x, cx, iy = 162;
    u16 fg;

    // [play / pausa]
    x = 4; cx = x + 19;
    fg = dk->playing ? C_DARK : C_LGRAY;
    btnFrame(x, dk->playing ? C_ORG : C_PANEL2);
    if (dk->playing) { rect(fb, cx - 8, iy, 5, 14, fg); rect(fb, cx + 3, iy, 5, 14, fg); }
    else             { fillTri(cx - 6, iy, +1, fg); }
    btnLabel(x, dk->playing ? "PAUSA" : "PLAY", fg);

    // [loop]: corchetes
    x = 46; cx = x + 19;
    fg = loopEdit ? C_DARK : C_LGRAY;
    btnFrame(x, loopEdit ? C_YEL : C_PANEL2);
    rect(fb, cx - 13, iy, 3, 14, fg); rect(fb, cx - 13, iy, 6, 3, fg); rect(fb, cx - 13, iy + 11, 6, 3, fg);
    rect(fb, cx + 10, iy, 3, 14, fg); rect(fb, cx + 7, iy, 6, 3, fg);  rect(fb, cx + 7, iy + 11, 6, 3, fg);
    rect(fb, cx - 3, iy + 5, 6, 4, fg);
    btnLabel(x, loopEdit ? "EDITAR" : "LOOP", fg);

    // [al inicio]: barra + triangulo a la izquierda
    x = 88; cx = x + 19;
    fg = C_LGRAY;
    btnFrame(x, C_PANEL2);
    rect(fb, cx - 12, iy, 3, 14, fg);
    fillTri(cx + 8, iy, -1, fg);
    btnLabel(x, "INICIO", fg);

    // [carpeta]: carga un audio en el deck activo
    x = 130; cx = x + 19;
    fg = C_LGRAY;
    btnFrame(x, C_PANEL2);
    rect(fb, cx - 12, iy + 1, 9, 3, fg);
    rect(fb, cx - 12, iy + 4, 24, 10, fg);
    btnLabel(x, actDeck ? "SD > B" : "SD > A", fg);

    // [TODO]: loop = track completo (marco)
    x = 172; cx = x + 19;
    fg = C_LGRAY;
    btnFrame(x, C_PANEL2);
    rect(fb, cx - 12, iy, 24, 14, fg);
    rect(fb, cx - 9, iy + 3, 18, 8, C_PANEL2);
    btnLabel(x, "TODO", fg);

    // [PANT.]: intercambia las dos pantallas (dos marcos apilados)
    x = 214; cx = x + 19;
    fg = C_LGRAY;
    btnFrame(x, C_PANEL2);
    rect(fb, cx - 9, iy, 18, 6, fg); rect(fb, cx - 7, iy + 2, 14, 2, C_PANEL2);
    rect(fb, cx - 9, iy + 8, 18, 6, fg);
    btnLabel(x, "PANT.", fg);

    lastPlaying = dk->playing;
    lastLoopOn = loopEdit;
    lastDrop = false;
    lastAct = actDeck;
}

static void updateView(u32 lead) {
    View v[2];
    for (int di = 0; di < 2; di++) v[di] = viewOf(&decks[di], heardPosD(&decks[di], lead));
    if (fullRedraw) {
        clearScreen(fb, C_BG);
        for (int di = 0; di < 2; di++) drawRows(di, 0, PH - 1, &v[di]);
        drawTags(); drawXfade(); drawButtons();
        fullRedraw = false;
    } else {
        for (int di = 0; di < 2; di++) {
            const View *o = &lastV[di], *n = &v[di];
            bool loopCh = (n->lon != o->lon) || (n->lon && (n->ls != o->ls || n->le != o->le));
            if (loopCh) {
                drawRows(di, 0, PH - 1, n);
            } else if (n->cy != o->cy || n->spr != o->spr || n->gh != o->gh || n->drop != o->drop) {
                int e0 = o->gh > o->spr ? o->gh : o->spr, e1 = n->gh > n->spr ? n->gh : n->spr;
                int a0 = o->cy - o->spr, b0 = o->cy + e0, a1 = n->cy - n->spr, b1 = n->cy + e1;
                drawRows(di, a0 < a1 ? a0 : a1, b0 > b1 ? b0 : b1, n);   // solo lo que cambio
            }
        }
        if (actDeck != lastAct) drawTags();
        if (xfade != lastXf) drawXfade();
        if (dk->playing != lastPlaying || loopEdit != lastLoopOn || actDeck != lastAct) drawButtons();
    }
    lastV[0] = v[0]; lastV[1] = v[1];
    { static u32 gc = 0; if ((++gc & 3) == 0 || fullRedraw) drawGrains(); }   // marcas de granos a ~15 fps
}

// donde esta la cabeza segun lo que SE ESCUCHA (el audio se renderiza ~47 ms por delante)
static s32 heardPosD(Deck *d, u32 ahead) {
    s32 h;
    if (d->dropOn || d->mixQ > MIX_FULL / 2) {              // se oye sobre todo el track limpio
        h = d->trackI;
        if (d->playing) h -= (s32)(((u32)ahead * d->cleanInc) >> 16);
    } else {
        h = d->posI;
        if (d->playing && !(touching && d == dk) && !(freezeKey && d == dk)) h -= (s32)(((s32)ahead * d->scanInc) >> 16);
    }
    return clampi(h, 0, (s32)d->srcLen - 1);
}

// ---------------------------------------------------------------- anillo de audio
// El indice de escritura siempre queda alineado a CHUNK (si no, el ultimo bloque de cada vuelta
// se sale del buffer y deja un hueco con audio viejo).
static inline u32 ringSync(u32 ph) { return (ph + LEAD) & ~(u32)(CHUNK - 1) & (OUT_LEN - 1); }

// adelanto de escritura sobre el playhead, en ticks del timer (16 por muestra) y con signo:
// al contar los ticks que pasaron entre cuadros, un tiron largo se detecta (leadT < 0) aunque
// el indice del anillo ya haya dado la vuelta
static s32 leadT = LEAD * 16;
static s32 leadGoal = LEAD * 16;      // durante una carga sube a ~100 ms para aguantar las lecturas lentas de la SD
static u32 tPrev = 0, ringResyncs = 0;

static void ringReset(u32 *wr, u32 t) {
    u32 ph = (t >> 4) & (OUT_LEN - 1);
    *wr = ringSync(ph);
    leadT = (s32)(((*wr - ph) & (OUT_LEN - 1)) * 16);
    tPrev = t;
    ringResyncs++;
}

// renderiza por delante del playhead; si el playhead nos alcanzo (hubo un tiron) resincroniza
static u32 okChunks = 0;
static u32 pump(u32 wr, u32 t) {
    leadT -= (s32)((t - tPrev) & 0xFFFF);
    tPrev = t;
    if (leadT < 0) {                               // nos alcanzo el playhead: hubo sobrecarga
        ringReset(&wr, t);
        if (grainCap > 4) grainCap -= 2;
        okChunks = 0;
    }
    while (leadT < leadGoal) {
        u16 c0 = TIMER_DATA(0);
        render(&outL[wr], &outR[wr], CHUNK);
        u16 used = (u16)(TIMER_DATA(0) - c0);       // ticks gastados (presupuesto: 16 por muestra = 4096 por tanda)
        if (used > 3000) { if (grainCap > 4) grainCap--; okChunks = 0; }
        else if (used < 2000 && ++okChunks > 600) { if (grainCap < MAX_GRAINS) grainCap++; okChunks = 0; }
        DC_FlushRange(&outL[wr], CHUNK * 2);
        DC_FlushRange(&outR[wr], CHUNK * 2);
        wr = (wr + CHUNK) & (OUT_LEN - 1);
        leadT += CHUNK * 16;
    }
    return wr;
}

static u32 ringWr = LEAD;
static void audioTick(void) { ringWr = pump(ringWr, TIMER_DATA(0)); }

// ---------------------------------------------------------------- main
int main(void) {
    // las dos pantallas son bitmaps de 16 bit: arriba parametros, abajo forma de onda y botones
    videoSetMode(MODE_5_2D | DISPLAY_BG3_ACTIVE);
    videoSetModeSub(MODE_5_2D | DISPLAY_BG3_ACTIVE);
    vramSetBankA(VRAM_A_MAIN_BG);
    vramSetBankC(VRAM_C_SUB_BG);
    int bgMain = bgInit(3, BgType_Bmp16, BgSize_B16_256x256, 0, 0);
    int bgSub  = bgInitSub(3, BgType_Bmp16, BgSize_B16_256x256, 0, 0);
    fbTop = (u16 *)bgGetGfxPtr(bgMain);
    fb    = (u16 *)bgGetGfxPtr(bgSub);
    clearScreen(fbTop, C_BG);
    clearScreen(fb, C_BG);

    sdOK = fatInitDefault();
    soundEnable();

    for (int i = 0; i < OUT_LEN; i++) outL[i] = outR[i] = 0;
    // sample inicial: sierra ~220 Hz con decaimiento, para sonar antes de cargar nada
    for (int i = 0; i < DEMO_LEN; i++)
        demoBuf[i] = (s8)(((((i % 73) * 400 - 14600) * (DEMO_LEN - i)) / DEMO_LEN) >> 8);
    for (int i = 0; i < WIN_LEN; i++)        // ventana Hann en Q15
        win[i] = (s16)(32767.0f * 0.5f * (1.0f - cosf(6.2831853f * i / (WIN_LEN - 1))));
    win[WIN_LEN] = 0;
    harmRatio[0] = (s32)(65536.0f * exp2f(-12.0f / 12.0f));
    harmRatio[1] = (s32)(65536.0f * exp2f(-5.0f / 12.0f));
    harmRatio[2] = (s32)(65536.0f * exp2f(7.0f / 12.0f));
    harmRatio[3] = (s32)(65536.0f * exp2f(12.0f / 12.0f));
    initTables();
    updateDelay();
    dtCur = dtTgt;
    updateReverb();
    updateFlutter();
    for (int i = 0; i < 2; i++) {                    // los dos decks arrancan con el demo; A suena, B espera
        dk = &decks[i];
        dk->speedPct = 100; dk->semis = 0;
        dk->heapBuf = NULL;
        useDemo("[demo]");
        dk->playing = (i == 0);
    }
    dk = &decks[0];
    setXfade(0);
    setPage(0);
    selectKnob(0);

    DC_FlushRange(outL, sizeof(outL));
    DC_FlushRange(outR, sizeof(outR));
    // dos canales mono, uno a cada lado: eso da el estereo
    soundPlaySample(outL, SoundFormat_16Bit, sizeof(outL), OUT_RATE, 127, 0, true, 0);
    soundPlaySample(outR, SoundFormat_16Bit, sizeof(outR), OUT_RATE, 127, 127, true, 0);

    // reloj del playhead: 33.514 MHz / 64 = 523656 Hz = 16 ticks por muestra de salida
    TIMER_DATA(0) = 0;
    TIMER_CR(0) = TIMER_ENABLE | TIMER_DIV_64;

    u32 frame = 0;
    tPrev = TIMER_DATA(0);
    leadT = LEAD * 16;
    ringWr = LEAD;
    bool uiDirty = true;
    keysSetRepeat(15, 3);

    while (1) {
        swiWaitForVBlank();
        scanKeys();
        u32 kd = keysDown(), kh = keysHeld(), kr = keysDownRepeat();
        if (kd | kr) uiDirty = true;

        if (browsing) {
            touching = false; freezeKey = false; touchDrag = false;
            bool dirty = false;
            if ((kr & KEY_UP)   && sel > 0)        { sel--; dirty = true; }
            if ((kr & KEY_DOWN) && sel < nEnt - 1) { sel++; dirty = true; }
            if (sel < scrollTop) scrollTop = sel;
            if (sel >= scrollTop + BR_ROWS) scrollTop = sel - (BR_ROWS - 1);
            if (kd & KEY_B) { browsing = false; topFull = true; fullRedraw = true; }
            else if ((kd & KEY_A) && nEnt > 0) {
                if (ents[sel].dir) {
                    if (chdir(ents[sel].name) == 0) scanDir();
                    dirty = true;
                } else {
                    // el deck que se carga se detiene; el otro sigue sonando (loadWav bombea el audio)
                    dk->playing = false;
                    leadGoal = 3328 * 16;                         // colchon grande: el otro deck no se corta
                    audioTick();
                    drawLoadScreen(ents[sel].name);
                    const char *err = loadWav(ents[sel].name);
                    audioTick();
                    leadGoal = LEAD * 16;
                    if (err) {
                        if (dk->lostSample) useDemo("[demo]");   // la carga fallida nos dejo sin sample
                        dk->playing = false;
                        drawErrorScreen(err);
                        while (1) { swiWaitForVBlank(); scanKeys(); audioTick(); if (keysDown() & (KEY_A | KEY_B)) break; }
                        dirty = true;
                    } else {
                        browsing = false;
                        topFull = true;
                    }
                    fullRedraw = true;
                    uiDirty = true;
                }
            }
            if (dirty && browsing) drawBrowser();
        } else {
            freezeKey = (kh & KEY_B) != 0;
            if (kd & KEY_START)  togglePlay();
            if (kd & KEY_A)      doSwap();
            if (kd & KEY_SELECT) { actDeck ^= 1; dk = &decks[actDeck]; fullRedraw = true; topFull = true; }
            if (kd & KEY_X)      setPage(kPage - 1);
            if (kd & KEY_Y)      setPage(kPage + 1);
            if (kr & KEY_L)      setXfade(xfade - 8);
            if (kr & KEY_R)      setXfade(xfade + 8);
            if (kr & KEY_LEFT)   moveKnob(-1);
            if (kr & KEY_RIGHT)  moveKnob(+1);
            if (kr & KEY_UP)     adjust(+1);
            if (kr & KEY_DOWN)   adjust(-1);

            // pantalla tactil: lo que este abajo (ondas o knobs) responde al stylus
            if (kh & KEY_TOUCH) {
                touchPosition t;
                touchRead(&t);
                if (kd & KEY_TOUCH) {
                    touchDrag = false; xfDrag = false; kDrag = -1;
                    if (swapped) {                                   // knobs abajo
                        if (t.py >= TAB_Y) {
                            if (t.px < 90) setPage(0); else if (t.px < 180) setPage(1); else doSwap();
                        } else if (t.py >= KY0 && t.py < KY0 + 2 * KCH) {
                            int k = ((t.py - KY0) / KCH) * 4 + t.px / 64;
                            if (knobAt(kPage, k) >= 0) { selectKnob(k); kDrag = k; kY0 = t.py; kDone = 0; }
                        } else if (t.py >= PNL_Y && t.py < PNL_Y + PNL_H) {
                            int dd = t.px < 128 ? 0 : 1;
                            if (dd != actDeck) { actDeck = dd; dk = &decks[dd]; fullRedraw = true; topFull = true; }
                        }
                    } else if (t.py >= BAR_Y) {                      // botones de las ondas
                        if (t.px < 44)       togglePlay();
                        else if (t.px < 86)  toggleLoop();
                        else if (t.px < 128) seekTo(dk->loopStart);
                        else if (t.px < 170) openBrowser();
                        else if (t.px < 212) { dk->loopStart = 0; dk->loopEnd = (s32)dk->srcLen - 1; }
                        else                 doSwap();
                    } else if (t.py >= XF_Y - 2) {
                        xfDrag = true;
                    } else {                                          // columnas de ondas (o etiquetas A / B)
                        int dd = t.px < 128 ? 0 : 1;
                        if (dd != actDeck) { actDeck = dd; dk = &decks[dd]; fullRedraw = true; topFull = true; }
                        if (t.py >= TOPY) {
                            touchDrag = true;
                            if (loopEdit) {
                                loopAnchor = clampi(t.py - TOPY, 0, PH - 1);
                                loopAnchor = (s32)((u32)loopAnchor * (dk->srcLen - 1) / (PH - 1));
                            }
                        }
                    }
                }
                if (xfDrag) setXfade((t.px - 20) * 256 / 216);
                if (kDrag >= 0) {                                    // arrastre vertical sobre un knob: 2 px por paso
                    int want = (kY0 - t.py) / 2;
                    while (kDone < want) { adjust(+1); kDone++; }
                    while (kDone > want) { adjust(-1); kDone--; }
                }
                if (touchDrag) {
                    s32 r = clampi(t.py - TOPY, 0, PH - 1);
                    s32 idx = (s32)((u32)r * (dk->srcLen - 1) / (PH - 1));
                    if (loopEdit) {                                   // el stylus arrastra y delimita el loop
                        dk->loopStart = idx < loopAnchor ? idx : loopAnchor;
                        dk->loopEnd   = idx < loopAnchor ? loopAnchor : idx;
                        fixLoop(true);
                    } else seekTo(idx);
                }
            } else {
                if (touchDrag && loopEdit && (dk->posI < dk->loopStart || dk->posI >= dk->loopEnd)) seekTo(dk->loopStart);
                touchDrag = false; xfDrag = false; kDrag = -1;
            }
            touching = touchDrag;
        }

        // pantallas primero: justo despues del vblank no se ven cortes
        s32 lt = leadT - (s32)((TIMER_DATA(0) - tPrev) & 0xFFFF);
        u32 lead = lt > 0 ? (u32)lt / 16 : 0;
        updateView(lead);
        audioTick();
        if (!browsing) {
            if (uiDirty || (++frame % 6) == 0) { drawKView(lead); uiDirty = false; }
        }

        // audio: renderiza por delante del playhead
        audioTick();
    }
    return 0;
}
