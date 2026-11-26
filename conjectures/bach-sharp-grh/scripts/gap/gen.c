// g(q): least prime y such that the primes <= y not dividing q generate (Z/q)^*,
// by the Frattini rank test: for every prime l | phi(q), the images in G/G^l span.
// Reads q per line from stdin; prints q g(q) ratio=g/log^2 q, flags q with g > c log^2 q.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef unsigned long long u64; typedef __uint128_t u128;
static u64 mulm(u64 a, u64 b, u64 m) { return (u128)a * b % m; }
static u64 powm(u64 a, u64 e, u64 m) { u64 r = 1 % m; a %= m; while (e) { if (e & 1) r = mulm(r, a, m); a = mulm(a, a, m); e >>= 1; } return r; }
static int sp[200000], nsp;
static int factor(u64 n, u64 *ps, int *es) { int k = 0;
  for (int i = 0; i < nsp && (u64)sp[i] * sp[i] <= n; i++) if (n % sp[i] == 0) { ps[k] = sp[i]; es[k] = 0; while (n % sp[i] == 0) { n /= sp[i]; es[k]++; } k++; }
  if (n > 1) { // n has no factor <= sp[nsp-1]; assume prime if n < sp^2
    ps[k] = n; es[k] = 1; k++; }
  return k; }
// components
typedef struct { u64 mod, n; int two; } Comp; // two: 0 odd cyclic order n; 1: 2^e, e>=3 handled as two comps
static Comp C[64]; static int nc;
static u64 L[64]; static int nl; // primes dividing phi
// per l: list of comps (index) with l | n, and zeta, and basis
typedef struct { int nc; int ci[64]; u64 zeta[64]; u64 e[64]; int rank; u64 basis[64][64]; int piv[64]; } LS;
static LS ls[64];
static u64 dlog(u64 u, u64 z, u64 l, u64 m) { // u = z^k, k < l
  u64 t = 1; for (u64 k = 0; k < l; k++) { if (t == u) return k; t = mulm(t, z, m); } return (u64)-1; }
static u64 inv_l(u64 a, u64 l) { return powm(a, l - 2, l); }
int main(int argc, char **argv) {
  double cmax = argc > 1 ? atof(argv[1]) : 2.0 / (log(3) * log(3));
  for (int n = 2; n < 2700000; n++) { int ok = 1; for (int i = 0; i < nsp && sp[i] * sp[i] <= n; i++) if (n % sp[i] == 0) { ok = 0; break; } if (ok) sp[nsp++] = n; if (nsp >= 200000) break; }
  u64 q; double worst = 0; u64 worstq = 0; u64 cnt = 0, bad = 0; int maxr = 0; u64 maxl_rank2 = 0;
  while (scanf("%llu", &q) == 1) {
    cnt++;
    u64 ps[64]; int es[64]; int k = factor(q, ps, es);
    nc = 0;
    for (int i = 0; i < k; i++) { u64 p = ps[i]; u64 pe = 1; for (int j = 0; j < es[i]; j++) pe *= p;
      if (p == 2) { if (es[i] == 2) { C[nc].mod = 4; C[nc].n = 2; C[nc].two = 2; nc++; }
        else if (es[i] >= 3) { C[nc].mod = pe; C[nc].n = 2; C[nc].two = 3; nc++; // a mod 4 sign
          C[nc].mod = pe; C[nc].n = pe / 4; C[nc].two = 4; nc++; } }
      else { C[nc].mod = pe; C[nc].n = pe / p * (p - 1); C[nc].two = 0; nc++; } }
    // primes l dividing some n
    nl = 0;
    for (int i = 0; i < nc; i++) { u64 ps2[64]; int es2[64]; int k2 = factor(C[i].n, ps2, es2);
      for (int j = 0; j < k2; j++) { int f = 0; for (int t = 0; t < nl; t++) if (L[t] == ps2[j]) f = 1; if (!f) L[nl++] = ps2[j]; } }
    for (int t = 0; t < nl; t++) { LS *s = &ls[t]; s->nc = 0; s->rank = 0; u64 l = L[t];
      for (int i = 0; i < nc; i++) if (C[i].n % l == 0) { s->ci[s->nc] = i; s->zeta[s->nc] = 0; s->e[s->nc] = C[i].n / l; s->nc++; } }
    // coordinate of a in comp i for prime l: for odd: a^(n/l) mod p^e. two=2: a mod 4 ==3. two=3: a mod 4==3 ; two=4 (cyclic <5> of order 2^(e-2)): b = a or -a with b = 1 mod 4, then b^(n/2) mod 2^e
    int done = 0; u64 g = 0;
    for (int si = 0; si < nsp && !done; si++) { u64 a = sp[si]; if (q % a == 0) continue;
      done = 1;
      for (int t = 0; t < nl; t++) { LS *s = &ls[t]; u64 l = L[t]; if (s->rank == s->nc) continue;
        u64 v[64];
        for (int j = 0; j < s->nc; j++) { Comp *c = &C[s->ci[j]]; u64 u;
          if (c->two == 2 || c->two == 3) { v[j] = (a % 4 == 3); continue; }
          if (c->two == 4) { u64 b = (a % 4 == 1) ? a % c->mod : c->mod - a % c->mod; u = powm(b, s->e[j], c->mod); }
          else u = powm(a, s->e[j], c->mod);
          if (u == 1) { v[j] = 0; continue; }
          if (s->zeta[j] == 0) s->zeta[j] = u;
          if (s->nc == 1) { v[j] = 1; continue; }
          v[j] = dlog(u, s->zeta[j], l, c->mod); if (v[j] == (u64)-1) { fprintf(stderr, "dlog fail q=%llu\n", q); exit(1); } }
        // reduce
        for (int r = 0; r < s->rank; r++) { int p = s->piv[r]; if (v[p]) { u64 f = v[p]; for (int j = 0; j < s->nc; j++) v[j] = (v[j] + (l - f) % l * s->basis[r][j]) % l; } }
        int p = -1; for (int j = 0; j < s->nc; j++) if (v[j]) { p = j; break; }
        if (p >= 0) { u64 iv = inv_l(v[p], l); for (int j = 0; j < s->nc; j++) s->basis[s->rank][j] = mulm(v[j], iv, l);
          // keep reduced: eliminate pivot from previous rows
          for (int r = 0; r < s->rank; r++) { u64 f = s->basis[r][p]; if (f) for (int j = 0; j < s->nc; j++) s->basis[r][j] = (s->basis[r][j] + (l - f) * s->basis[s->rank][j]) % l; }
          s->piv[s->rank++] = p; }
        if (s->rank < s->nc) done = 0;
        if (s->nc > maxr) maxr = s->nc; if (s->nc >= 2 && l > maxl_rank2) maxl_rank2 = l; }
      if (done) g = a; }
    double L2 = log((double)q) * log((double)q); double r = g / L2;
    if (r > worst) { worst = r; worstq = q; }
    if (g > cmax * L2) { bad++; printf("BAD %llu g=%llu bound=%.3f\n", q, g, cmax * L2); }
    if (argc > 2) printf("%llu %llu %.5f\n", q, g, r);
  }
  fprintf(stderr, "count %llu bad %llu worst ratio %.5f at q=%llu maxrank %d max l with rank>=2: %llu\n", cnt, bad, worst, worstq, maxr, maxl_rank2);
}
