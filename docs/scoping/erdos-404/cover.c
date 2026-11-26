/* cover.c -- exact subset-sum coverage of factorial-type sets modulo p^D,
 * using a top-down "periodic window" sumset.
 *
 * Elements: a finite list of integers x_i = p^{k_i} * u_i  (u_i a p-adic unit).
 * T_k := { subset sums of the x_i with k_i >= k }  (mod p^D).
 * Fact: if T_m = p^m Z/p^D Z (full), then T_k is p^m-periodic for k < m, so T_k
 * is determined by U_k = T_k / p^k  mod p^{m-k}  (a subset of Z/p^w, w = m-k).
 * Going down one level:  U_k = (p * U_{k+1}) + subsetsums(u_i : k_i = k)  mod p^w.
 * If U_k is all of Z/p^w, T_k is full and we reset m := k (w = 0).
 * This is exact: no approximation.
 *
 * Modes
 *   cover tail  p D nmin [target]   elements n!  for nmin <= n, v_p(n!) < D
 *   cover block p N H [extra]        elements (N+j)!/N!, 0<=j<H, modulus p^{v_p((N+H)!/N!)+extra}
 * Prints: whether full coverage holds at the bottom level, coverage fraction of the
 * bottom window, whether target (default -1 i.e. -1!) is reachable, and window stats.
 * Options via env: WCAP (max window digits, default chosen by p), VERBOSE=1.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;

static int P;
static u64 PW[64];
static int WCAP;

static int vp(u64 n) { int v = 0; while (n % P == 0) { n /= P; v++; } return v; }

/* bitset over Z/p^w */
typedef struct { u64 *b; u64 M; size_t nw; } bs;
static bs bs_new(u64 M) { bs s; s.M = M; s.nw = (M + 63) / 64 + 2; s.b = calloc(s.nw, 8); if (!s.b) { fprintf(stderr, "oom\n"); exit(2);} return s; }
static void bs_free(bs *s) { free(s->b); s->b = 0; }
static inline int bs_get(const bs *s, u64 i) { return (s->b[i >> 6] >> (i & 63)) & 1; }
static inline void bs_set(bs *s, u64 i) { s->b[i >> 6] |= 1ULL << (i & 63); }
static u64 bs_count(const bs *s) {
  u64 c = 0; size_t full = s->M / 64;
  for (size_t i = 0; i < full; i++) c += __builtin_popcountll(s->b[i]);
  if (s->M & 63) c += __builtin_popcountll(s->b[full] & ((1ULL << (s->M & 63)) - 1));
  return c;
}
/* read up to 64 bits starting at bit pos (no wrap; caller ensures pos+len<=M) */
static inline u64 rd(const bs *s, u64 pos, int len) {
  if (len == 0) return 0;
  size_t w = pos >> 6; int o = pos & 63;
  u64 x = s->b[w] >> o;
  if (o && o + len > 64) x |= s->b[w + 1] << (64 - o);
  if (len < 64) x &= (1ULL << len) - 1;
  return x;
}
/* read len bits starting at pos with wrap modulo M */
static inline u64 rdw(const bs *s, u64 pos, int len) {
  if (pos + len <= s->M) return rd(s, pos, len);
  int a = (int)(s->M - pos);
  u64 lo = rd(s, pos, a);
  u64 hi = rdw(s, 0, len - a);
  return lo | (hi << a);
}
/* dst = src | rot(src, e)   (dst != src) */
static void bs_or_rot(bs *dst, const bs *src, u64 e) {
  u64 M = src->M;
  for (u64 i = 0; i * 64 < M; i++) {
    u64 base = i * 64; int len = (M - base >= 64) ? 64 : (int)(M - base);
    u64 start = (base + M - e % M) % M;
    dst->b[i] = src->b[i] | rdw(src, start, len);
  }
}

typedef struct { int k; u64 u; } elt; /* x = p^k * u, u unit mod p^WCAP */

static int maxw_seen = 0; static long maxw_level = -1;
static long nresets = 0;
static int verbose = 0;
static FILE *exf = 0; /* excursion log */


/* Run the top-down window on elements sorted by k descending (any order inside a level).
 * D = modulus exponent, kbot = bottom level to report. Returns window state at kbot. */
static int run(elt *E, long ne, int D, int kbot, bs *outU, int *outw) {
  /* group: iterate levels k = D-1 .. kbot */
  int w = 0; bs U = bs_new(1); bs_set(&U, 0);
  long idx = 0; /* E sorted descending by k */
  int skipped = 0, top = D; /* skipped levels in current excursion, level where it started */
  for (int k = D - 1; k >= kbot; k--) {
    /* lift: U (over Z/p^w) -> pU over Z/p^{w+1} */
    w++;
    if (w > WCAP) { fprintf(stderr, "window exceeded WCAP=%d at level %d\n", WCAP, k); return -1; }
    bs V = bs_new(PW[w]);
    for (u64 x = 0; x < PW[w - 1]; x++) if (bs_get(&U, x)) bs_set(&V, x * P);
    bs_free(&U); U = V;
    while (idx < ne && E[idx].k > k) idx++;
    if (!(idx < ne && E[idx].k == k)) skipped++;
    while (idx < ne && E[idx].k == k) {
      u64 e = E[idx].u % PW[w];
      bs T = bs_new(PW[w]);
      bs_or_rot(&T, &U, e);
      bs_free(&U); U = T; idx++;
    }
    if (w > maxw_seen) { maxw_seen = w; maxw_level = k; }
    u64 c = bs_count(&U);
    if (verbose) printf("level %d w=%d cover=%llu/%llu\n", k, w, (unsigned long long)c, (unsigned long long)PW[w]);
    if (c == PW[w]) {
      if (exf && w >= 2) fprintf(exf, "EXC top=%d bottom=%d width=%d skipped=%d\n", top, k, w, skipped);
      if (k > kbot) { bs_free(&U); U = bs_new(1); bs_set(&U, 0); w = 0; nresets++; }
      skipped = 0; top = k;
    }
  }
  *outU = U; *outw = w; return 0;
}

static int cmpk(const void *a, const void *b) { const elt *x = a, *y = b; return (y->k > x->k) - (y->k < x->k); }

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: cover tail p D nmin [target] | cover block p N H\n"); return 1; }
  P = atoi(argv[2]);
  PW[0] = 1; int maxpw = 0;
  for (int i = 1; i < 64; i++) { u128 t = (u128)PW[i - 1] * P; if (t >> 62) break; PW[i] = (u64)t; maxpw = i; }
  WCAP = getenv("WCAP") ? atoi(getenv("WCAP")) : (P == 3 ? 19 : P == 5 ? 12 : P == 7 ? 10 : 8);
  verbose = getenv("VERBOSE") ? atoi(getenv("VERBOSE")) : 0;
  if (getenv("EXCLOG")) exf = fopen(getenv("EXCLOG"), "w");
  int UD = maxpw; /* unit precision digits */
  if (WCAP > UD) WCAP = UD;
  while (WCAP > 1 && PW[WCAP] > (1ULL << 33)) WCAP--; /* memory guard: <= 1 GB per bitset */
  u64 MOD = PW[UD];
  elt *E = 0; long ne = 0; int D = 0, kbot = 0; long long target = -1; int have_target = 0;
  if (!strcmp(argv[1], "tail")) {
    D = atoi(argv[3]); long nmin = atol(argv[4]);
    if (argc > 5) { target = atoll(argv[5]); have_target = 1; } else { have_target = 1; target = -1; }
    long cap = 1000; E = malloc(sizeof(elt) * cap);
    u64 u = 1; long vf = 0; /* n! = p^vf * u */
    for (long n = 0;; n++) {
      if (n > 0) { long m = n; int v = 0; while (m % P == 0) { m /= P; v++; } vf += v; u = (u64)((u128)u * (u64)(m % MOD) % MOD); }
      if (vf >= D) break;
      if (n >= nmin) { if (ne == cap) { cap *= 2; E = realloc(E, sizeof(elt) * cap); } E[ne].k = (int)vf; E[ne].u = u; ne++; }
    }
    kbot = 0;
  } else if (!strcmp(argv[1], "block")) {
    u64 N = strtoull(argv[3], 0, 10); long H = atol(argv[4]); int extra = argc > 5 ? atoi(argv[5]) : 0;
    E = malloc(sizeof(elt) * H);
    u64 u = 1; long vf = 0;
    for (long j = 0; j < H; j++) {
      if (j > 0) { u64 m = N + j; int v = 0; while (m % P == 0) { m /= P; v++; } vf += v; u = (u64)((u128)u * (m % MOD) % MOD); }
      E[ne].k = (int)vf; E[ne].u = u; ne++;
    }
    { u64 m = N + H; while (m % P == 0) { m /= P; vf++; } }
    D = (int)vf + extra; kbot = 0; have_target = 0;
  } else { fprintf(stderr, "bad mode\n"); return 1; }
  qsort(E, ne, sizeof(elt), cmpk);
  bs U; int w;
  if (run(E, ne, D, kbot, &U, &w) < 0) { printf("RESULT p=%d D=%d n_elts=%ld ABORT maxw>%d\n", P, D, ne, WCAP); return 3; }
  u64 c = bs_count(&U);
  int full = (c == PW[w]);
  printf("RESULT p=%d D=%d n_elts=%ld bottom_window=%d covered=%llu/%llu full=%d maxw=%d (at level %ld) resets=%ld",
         P, D, ne, w, (unsigned long long)c, (unsigned long long)PW[w], full, maxw_seen, maxw_level, nresets);
  if (have_target) {
    long long t = target % (long long)PW[w]; if (t < 0) t += PW[w];
    printf(" target=%lld reachable=%d", target, bs_get(&U, (u64)t));
  }
  printf("\n");
  if (getenv("DUMP") && w <= 8) { for (u64 x = 0; x < PW[w]; x++) if (!bs_get(&U, x)) printf("missing %llu\n", (unsigned long long)x); }
  return 0;
}
