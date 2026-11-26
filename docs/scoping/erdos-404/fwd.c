/* fwd.c -- forward carry DP for Erdos #404.
 *
 * Fix p, a, and a precision K. A state at stage N (terms a..N-1 decided, a always taken)
 * is the carry c = S_N / p^{v_p(N!)} mod p^{K - v_p(N!)}, kept only when p^{v_p(N!)} | S_N
 * (otherwise the partial sum can never be completed, since every later term is divisible
 * by p^{v_p(N!)}). Step N: c -> c or c + N!/p^{v(N!)}; then divide by p^{v(N+1)} (keeping
 * only states divisible by it). The set of states is a bitset over Z/p^w, w = K - v(N!).
 *
 *   fwd p a K [print_every]
 * Prints, at the end of every block (N+1 divisible by p) or every print_every stages,
 *   N, v(N!), w, |U|, density |U|/p^w, max j such that the pre-division set contains a
 *   multiple of p^j (used to get the exact value of f when the set dies).
 * If the set dies at stage N: f(a,p) = v(N!) + jmax (exact), provided this is < K.
 * If the run reaches w = 0 with a nonempty set: f(a,p) >= K.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static int P; static u64 PW[64];

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: fwd p a K [print_every]\n"); return 1; }
  P = atoi(argv[1]); long a = atol(argv[2]); int K = atoi(argv[3]); long pe = argc > 4 ? atol(argv[4]) : 0;
  int UD = 0; PW[0] = 1; for (int i = 1; i < 64; i++) { u128 t = (u128)PW[i-1] * P; if (t >> 62) break; PW[i] = (u64)t; UD = i; }
  u64 MOD = PW[UD];
  /* unit part and valuation of a! */
  u64 u = 1; long vf = 0;
  for (long n = 1; n <= a; n++) { long m = n; while (m % P == 0) { m /= P; vf++; } u = (u64)((u128)u * (u64)m % MOD); }
  int w = K - (int)vf;
  if (w <= 0) { printf("RESULT p=%d a=%ld K=%d trivially f>=K (v(a!)=%ld)\n", P, a, K, vf); return 0; }
  if (w > UD || PW[w] > (1ULL << 30)) { fprintf(stderr, "w=%d too large\n", w); return 2; }
  u64 M = PW[w];
  uint8_t *U = calloc(M, 1), *V = calloc(M, 1);
  /* stage N = a: decided nothing yet, but a is forced: add it then step */
  long N = a; int first = 1;
  for (;;) {
    /* add term N (forced if first) */
    u64 e = u % M;
    if (first) { memset(U, 0, M); U[e % M] = 1; first = 0; }
    else { memcpy(V, U, M); for (u64 x = 0; x < M; x++) if (V[x]) U[(x + e) % M] = 1; }
    /* divide by p^{v(N+1)} */
    long m = N + 1; int j = 0; while (m % P == 0) { m /= P; j++; }
    int jmax = 0; /* largest valuation present (capped at w) */
    for (u64 x = 0; x < M; x++) if (U[x]) { int vv = 0; u64 y = x; if (y == 0) vv = w; else while (y % P == 0) { y /= P; vv++; } if (vv > jmax) jmax = vv; }
    u64 cnt = 0;
    int nw = w - j;
    if (nw <= 0) {
      /* reached precision K: nonempty set containing a multiple of p^w means f >= K */
      int ok = 0; if (U[0]) ok = 1;
      printf("RESULT p=%d a=%ld K=%d reached N=%ld: %s\n", P, a, K, N + 1, ok ? "f>=K" : "dies");
      if (!ok) printf("RESULT exact f(%ld,%d) = %ld\n", a, P, vf + jmax);
      return 0;
    }
    u64 nM = PW[nw];
    memset(V, 0, nM);
    for (u64 x = 0; x < M; x += PW[j]) if (U[x]) { V[x / PW[j]] = 1; cnt++; }
    if (cnt == 0) {
      printf("RESULT p=%d a=%ld K=%d dies at N=%ld; exact f(%ld,%d) = %ld\n", P, a, K, N + 1, a, P, vf + jmax);
      return 0;
    }
    uint8_t *t = U; U = V; V = t; w = nw; M = nM; vf += j;
    if ((j > 0 && (pe == 0 || (N + 1) % pe == 0)) || (pe > 0 && (N + 1) % pe == 0))
      printf("N=%ld v=%ld w=%d states=%llu density=%.6f jump=%d\n", N + 1, vf, w, (unsigned long long)cnt, (double)cnt / (double)M, j);
    /* advance: unit part of (N+1)! */
    N++; u = (u64)((u128)u * (u64)(m % MOD) % MOD);
  }
}
