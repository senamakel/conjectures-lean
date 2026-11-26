/* OUTPROC for nauty gentreeg: for every free tree, compute
 *   D(T,x) domination polynomial (Alikhani-Peng unimodality, tree case)
 *   I(T,x) independence polynomial (log-concavity failures saved for forest search)
 * and report the worst "valley score" V = max_j min(max_{i<j} a_i, max_{k>j} a_k) / a_j
 * over positive coefficients (V > 1  <=>  not unimodal).
 * Tree DP, states for v: A = v in S; B = v not in S, dominated by a child;
 * C = v not in S, not dominated yet.  Coefficients fit in uint64 for n <= 62. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MX 64
typedef uint64_t u64;
static u64 cnt = 0, domviol = 0, indviol = 0, indnlc = 0, domnlc = 0;
static double worstD = 0, worstI = 0;
static int worstDpar[MX + 1], worstIpar[MX + 1], gn = 0;
static FILE *nlcf = NULL;

static void mul(u64 *r, int *rl, const u64 *a, int al, const u64 *b, int bl) {
    u64 t[MX + 2]; int l = al + bl - 1;
    memset(t, 0, sizeof(u64) * l);
    for (int i = 0; i < al; i++) if (a[i]) for (int j = 0; j < bl; j++) t[i + j] += a[i] * b[j];
    memcpy(r, t, sizeof(u64) * l); *rl = l;
}
static void add(u64 *r, int *rl, const u64 *a, int al, const u64 *b, int bl) {
    int l = al > bl ? al : bl;
    for (int i = 0; i < l; i++) r[i] = (i < al ? a[i] : 0) + (i < bl ? b[i] : 0);
    *rl = l;
}
static double valley(const u64 *a, int l) {
    int s = 0; while (s < l && a[s] == 0) s++;
    int e = l - 1; while (e >= 0 && a[e] == 0) e--;
    double best = 0; u64 pre[MX + 2], suf[MX + 2];
    pre[s] = a[s]; for (int i = s + 1; i <= e; i++) pre[i] = pre[i - 1] > a[i] ? pre[i - 1] : a[i];
    suf[e] = a[e]; for (int i = e - 1; i >= s; i--) suf[i] = suf[i + 1] > a[i] ? suf[i + 1] : a[i];
    for (int j = s + 1; j < e; j++) {
        u64 m = pre[j - 1] < suf[j + 1] ? pre[j - 1] : suf[j + 1];
        double v = (double)m / (double)a[j];  /* a[j] > 0 inside [s,e] for these polys */
        if (v > best) best = v;
    }
    return best;
}
static int notlc(const u64 *a, int l) {
    for (int j = 1; j + 1 < l; j++) {
        unsigned __int128 lhs = (unsigned __int128)a[j] * a[j], rhs = (unsigned __int128)a[j - 1] * a[j + 1];
        if (a[j - 1] && a[j + 1] && lhs < rhs) return 1;
    }
    return 0;
}
static void report(void) {
    fprintf(stderr, "n=%d trees=%llu domViolations=%llu indViolations=%llu domNotLC=%llu indNotLC=%llu worstValleyD=%.9f worstValleyI=%.9f\n",
            gn, (unsigned long long)cnt, (unsigned long long)domviol, (unsigned long long)indviol,
            (unsigned long long)domnlc, (unsigned long long)indnlc, worstD, worstI);
    fprintf(stderr, "worstD par:"); for (int j = 2; j <= gn; j++) fprintf(stderr, " %d", worstDpar[j]); fprintf(stderr, "\n");
    fprintf(stderr, "worstI par:"); for (int j = 2; j <= gn; j++) fprintf(stderr, " %d", worstIpar[j]); fprintf(stderr, "\n");
    if (nlcf) fclose(nlcf);
}

void treeproc(FILE *f, int *par, int n) {
    static u64 A[MX + 1][MX + 2], B[MX + 1][MX + 2], C[MX + 1][MX + 2];   /* domination */
    static u64 P[MX + 1][MX + 2], Q[MX + 1][MX + 2];                     /* independence: P in, Q out */
    static u64 AB[MX + 1][MX + 2];                                        /* prod (A_c + B_c) */
    static int la[MX + 1], lb[MX + 1], lc[MX + 1], lab[MX + 1], lp[MX + 1], lq[MX + 1];
    if (!gn) { gn = n; atexit(report); const char *fn = getenv("NLCFILE"); if (fn) nlcf = fopen(fn, "w"); }
    cnt++;
    for (int v = 1; v <= n; v++) {
        /* A_v = x * prod(A+B+C); start with x */
        A[v][0] = 0; A[v][1] = 1; la[v] = 2;
        AB[v][0] = 1; lab[v] = 1;      /* prod (A_c+B_c) */
        C[v][0] = 1; lc[v] = 1;        /* prod B_c */
        P[v][0] = 0; P[v][1] = 1; lp[v] = 2;
        Q[v][0] = 1; lq[v] = 1;
    }
    for (int j = n; j >= 2; j--) {
        int p = par[j];
        if (p >= j) { fprintf(stderr, "parent order assumption broken\n"); exit(2); }
        /* finalize j: B_j = AB_j - C_j */
        u64 Bj[MX + 2]; int lbj = lab[j];
        for (int i = 0; i < lbj; i++) Bj[i] = AB[j][i] - (i < lc[j] ? C[j][i] : 0);
        u64 t[MX + 2]; int lt, lt2; u64 t2[MX + 2];
        add(t, &lt, A[j], la[j], Bj, lbj); add(t2, &lt2, t, lt, C[j], lc[j]);
        mul(A[p], &la[p], A[p], la[p], t2, lt2);
        mul(AB[p], &lab[p], AB[p], lab[p], t, lt);
        mul(C[p], &lc[p], C[p], lc[p], Bj, lbj);
        /* independence */
        mul(P[p], &lp[p], P[p], lp[p], Q[j], lq[j]);
        add(t, &lt, P[j], lp[j], Q[j], lq[j]);
        mul(Q[p], &lq[p], Q[p], lq[p], t, lt);
    }
    u64 D[MX + 2]; int ld; u64 B1[MX + 2];
    for (int i = 0; i < lab[1]; i++) B1[i] = AB[1][i] - (i < lc[1] ? C[1][i] : 0);
    add(D, &ld, A[1], la[1], B1, lab[1]);
    u64 I[MX + 2]; int li; add(I, &li, P[1], lp[1], Q[1], lq[1]);
    /* sanity: D(1) <= 2^n, I sums */
    static int dump = -1; if (dump < 0) dump = getenv("DUMP") != NULL;
    if (dump) {
        while (ld > 1 && D[ld - 1] == 0) ld--; while (li > 1 && I[li - 1] == 0) li--;
        for (int k = 0; k < ld; k++) printf(k ? " %llu" : "%llu", (unsigned long long)D[k]);
        printf(" |"); for (int k = 0; k < li; k++) printf(" %llu", (unsigned long long)I[k]); printf("\n");
    }
    double vd = valley(D, ld), vi = valley(I, li);
    if (vd > 1.0) { domviol++; fprintf(stdout, "DOMVIOL"); for (int k = 2; k <= n; k++) fprintf(stdout, " %d", par[k]); fprintf(stdout, "\n"); fflush(stdout); }
    if (vi > 1.0) { indviol++; fprintf(stdout, "INDVIOL"); for (int k = 2; k <= n; k++) fprintf(stdout, " %d", par[k]); fprintf(stdout, "\n"); fflush(stdout); }
    if (vd > worstD) { worstD = vd; memcpy(worstDpar, par, sizeof(int) * (n + 1)); }
    if (vi > worstI) { worstI = vi; memcpy(worstIpar, par, sizeof(int) * (n + 1)); }
    if (notlc(D, ld)) domnlc++;
    if (notlc(I, li)) {
        indnlc++;
        if (nlcf) { for (int k = 0; k < li; k++) fprintf(nlcf, "%llu ", (unsigned long long)I[k]); fprintf(nlcf, "| par"); for (int k = 2; k <= n; k++) fprintf(nlcf, " %d", par[k]); fprintf(nlcf, "\n"); }
    }
}
