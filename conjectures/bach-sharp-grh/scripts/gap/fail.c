// Phase A: moduli q in [lo, hi) failing lls-grh's per-modulus GRH budget at c = 1.657,
// found by enumerating bad squarefree kernels (not by looping over q).
// Budget (LLS/Bach2/Budget.lean, LLS/Numerics/Budget.lean, LLS/Defs.lean), float version:
//   B(q) = base2(x, Pc) - kap(x) log q - sum_{p | q, p <= x} W_p(x),  x = floor(c La^2).
// Usage: fail lo_log2 hi_mult w xcap out
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
#include <string.h>
typedef unsigned long long u64;
typedef __uint128_t u128;
#define NPR 6000
static int pr[NPR], npr;
static double W[NPR], LG[NPR], RHO[NPR];
static double ces[4000];
static double Bq; static u64 A, B; static int nx;
static FILE *out;
static u64 nfail = 0, nleaf = 0, nnode = 0, ndup = 0; static double sumq = 0; static u64 maxq = 0;
static double CC = 1.657;

static double lam(int n) { // von Mangoldt
  for (int i = 0; i < npr && pr[i] <= n; i++) if (n % pr[i] == 0) {
    int m = n; while (m % pr[i] == 0) m /= pr[i];
    return m == 1 ? log(pr[i]) : 0; }
  return 0; }

static double weight_prefix_stop(u64 q, u64 *P) { // canonical leaf of q
  double w = 0; u64 prod = 1;
  for (int i = 0; i < nx; i++) if (q % pr[i] == 0) { w += W[i]; prod *= pr[i]; if (w >= Bq) { *P = prod; return w; } }
  *P = 0; return w; }

static void leaf(u64 P) {
  nleaf++;
  u64 q0 = ((A + P - 1) / P) * P;
  for (u64 q = q0; q < B; q += P) {
    u64 Pc; weight_prefix_stop(q, &Pc);
    if (Pc != P) { ndup++; continue; }
    nfail++; sumq += (double)q; if (q > maxq) maxq = q;
    if (out) fprintf(out, "%llu\n", q);
  }
}

static void dfs(int i, u64 P, double w) {
  nnode++;
  if (w >= Bq) { leaf(P); return; }
  if (i >= nx) return;
  u64 R = (B - 1) / P;
  if ((u64)pr[i] > R) return;
  if (w + RHO[i] * log((double)R) < Bq) return;
  dfs(i + 1, P * pr[i], w + W[i]);
  dfs(i + 1, P, w);
}

int main(int argc, char **argv) {
  double lo_l2 = atof(argv[1]); double himul = atof(argv[2]); int wsh = atoi(argv[3]); int xcap = atoi(argv[4]);
  if (argc > 5) out = fopen(argv[5], "w");
  if (argc > 6) CC = atof(argv[6]);
  for (int n = 2; npr < NPR && n < 60000; n++) { int ok = 1; for (int d = 2; d * d <= n; d++) if (n % d == 0) { ok = 0; break; } if (ok) pr[npr++] = n; }
  for (int x = 1; x < 4000; x++) { double s = 0; for (int n = 1; n <= x; n++) s += lam(n) * (1.0 / n) * (1 - (double)n / x); ces[x] = s; }
  u64 lo = (u64)pow(2, lo_l2), hi = (u64)(himul);
  const double g = 0.5772156649015329, lpi = log(M_PI);
  u64 a = lo; u64 nblk = 0; double worstmargin = 1e9;
  while (a < hi) {
    u64 b = a + ((a >> wsh) > 1 ? (a >> wsh) : 1); if (b > hi) b = hi;
    double La = log((double)a), Lb = log((double)b);
    int x = (int)floor(CC * La * La); if (x > xcap) x = xcap;
    double s = sqrt(x), l = log(x);
    double K = (s + 1 + l / 2) / (1 + 1.0 / x - 2 / s), kap = K * (1 - 1.0 / x) + l / 2;
    double Es = -0.5 * (1 - 1.0 / x) * lpi - g / 2 * (1 - 1.0 / x) + (l + 2) / x;
    double Et = M_PI * M_PI / 6 - g / 2 * l;
    double Pc = x < 2000 ? ces[x] : l - 2;
    double base = x - 0.15 * s - 3 * l - 3 + 2 * K * Pc - 2 * K * Es + 0.5 * lpi * l - Et;
    Bq = base - kap * Lb;
    nx = 0; while (nx < npr && pr[nx] <= x) nx++;
    for (int i = 0; i < nx; i++) { double lp = log(pr[i]); LG[i] = lp;
      double Ap = (l - lp / 2) * (l - lp / 2) / 2 + 2 * K * lp / (pr[i] - 1);
      W[i] = Ap + (Ap - kap * lp > 0 ? Ap - kap * lp : 0); }
    RHO[nx] = 0; for (int i = nx - 1; i >= 0; i--) { double r = W[i] / LG[i]; RHO[i] = r > RHO[i + 1] ? r : RHO[i + 1]; }
    A = a; B = b;
    dfs(0, 1, 0);
    nblk++; a = b;
  }
  fprintf(stderr, "blocks %llu nodes %llu leaves %llu fail %llu dup %llu sumq %.4g maxq %llu (2^%.3f)\n",
          nblk, nnode, nleaf, nfail, ndup, sumq, maxq, maxq ? log2((double)maxq) : 0);
  if (out) fclose(out);
}
