/* count.c -- multiplicity profile of subset sums of {n! : nmin <= n, v_p(n!) < k} mod p^k.
 *
 *   count p nmin kmax [target]
 * For each k = 1..kmax: let A_k = {n! : nmin <= n, v_p(n!) < k} (|A_k| = m elements).
 * Counts c(r) = #{subsets of A_k with sum = r mod p^k}, as doubles, normalised by the mean
 * 2^m / p^k. Prints: m, normalised count at the target (default -1, i.e. the a=1 problem:
 * c(-1) counts sets T with 1 in T, p^k | sum over T, all other elements in [nmin, ...)),
 * min and max normalised count over all residues, and the fraction of residues with c = 0.
 * Dense DP over Z/p^k; keep p^k <= ~6e7.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#ifndef REAL
#define REAL double
#endif
#ifndef MAXM
#define MAXM 70000000ULL
#endif
typedef unsigned __int128 u128; typedef uint64_t u64;
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: count p nmin kmax [target]\n"); return 1; }
  int p = atoi(argv[1]); long nmin = atol(argv[2]); int kmax = atoi(argv[3]);
  long long target = argc > 4 ? atoll(argv[4]) : -1;
  for (int k = 1; k <= kmax; k++) {
    u64 M = 1; for (int i = 0; i < k; i++) M *= p;
    if (M > MAXM) break;
    REAL *c = calloc(M, sizeof(REAL)), *d = calloc(M, sizeof(REAL));
    c[0] = 1.0; int m = 0;
    u64 f = 1 % M; long vf = 0;
    for (long n = 0;; n++) {
      if (n > 0) { long t = n; while (t % p == 0) { t /= p; vf++; } f = (u64)((u128)f * (u64)(n % M) % M); }
      if (vf >= k) break;
      if (n < nmin) continue;
      /* c <- c + shift(c, f), renormalised by 1/2 to keep the mean at 1/M */
      for (u64 x = 0; x < M; x++) { u64 y = x + f; if (y >= M) y -= M; d[y] = c[x]; }
      for (u64 x = 0; x < M; x++) c[x] = (REAL)0.5 * (c[x] + d[x]);
      m++;
    }
    double mn = 1e300, mx = 0; u64 zeros = 0;
    for (u64 x = 0; x < M; x++) { double v = c[x] * M; if (v < mn) mn = v; if (v > mx) mx = v; if (c[x] == 0) zeros++; }
    long long t = target % (long long)M; if (t < 0) t += M;
    printf("p=%d nmin=%ld k=%d m=%d  target_norm=%.4f  min_norm=%.4f  max_norm=%.4f  zero_frac=%.6f  log2(2^m/p^k)=%.1f\n",
           p, nmin, k, m, c[t] * M, mn, mx, (double)zeros / M, m - k * log2((double)p));
    free(c); free(d);
  }
  return 0;
}
