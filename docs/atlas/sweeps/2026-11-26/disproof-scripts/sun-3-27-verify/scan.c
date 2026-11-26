/* Independent classifier for N(e) = c*2^e + s, e = 1..Emax.
 * Written from scratch for the Sun 3.27 verification (2026-11-26).
 * Links against the system libgmp.so.10; the few GMP prototypes needed are
 * declared below because no gmp.h is installed on the build box.
 *
 * Output (one line per e, sorted):
 *   e F p        p is a prime dividing N(e) (p < N(e)); checkable by anyone
 *   e C fermat3-fail   3^(N-1) mod N != 1, so N is composite
 *   e P a        s == 1 only: Proth's theorem, a^((N-1)/2) == -1 mod N, so N is prime
 *   e Q          Fermat-3 PRP but no proof (only possible when s != 1)
 *   e X          PRP but no Proth witness found among a < 1000 (should never happen)
 *
 * usage: scan c s Emax B [elist-file]   (elist-file: restrict to those e)
 * build: gcc -O2 -fopenmp scan.c -o scan /usr/lib/x86_64-linux-gnu/libgmp.so.10
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

typedef struct { int alloc; int size; unsigned long *d; } mpz_s;
typedef mpz_s mpz_t[1];
void __gmpz_init(mpz_s *);
void __gmpz_clear(mpz_s *);
void __gmpz_set_ui(mpz_s *, unsigned long);
void __gmpz_set_si(mpz_s *, long);
void __gmpz_mul_2exp(mpz_s *, const mpz_s *, unsigned long);
void __gmpz_mul_ui(mpz_s *, const mpz_s *, unsigned long);
void __gmpz_add_ui(mpz_s *, const mpz_s *, unsigned long);
void __gmpz_sub_ui(mpz_s *, const mpz_s *, unsigned long);
void __gmpz_fdiv_q_2exp(mpz_s *, const mpz_s *, unsigned long);
void __gmpz_powm(mpz_s *, const mpz_s *, const mpz_s *, const mpz_s *);
int __gmpz_cmp(const mpz_s *, const mpz_s *);
int __gmpz_jacobi(const mpz_s *, const mpz_s *);
unsigned long __gmpz_tdiv_ui(const mpz_s *, unsigned long);

static long C, S;

static void buildN(mpz_s *N, long e) {
  __gmpz_set_ui(N, (unsigned long)C);
  __gmpz_mul_2exp(N, N, (unsigned long)e);
  if (S >= 0) __gmpz_add_ui(N, N, (unsigned long)S);
  else __gmpz_sub_ui(N, N, (unsigned long)(-S));
}

static unsigned long mulmod(unsigned long a, unsigned long b, unsigned long m) {
  return (unsigned long)((unsigned __int128)a * b % m);
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage\n"); return 1; }
  C = atol(argv[1]); S = atol(argv[2]);
  long Emax = atol(argv[3]); long B = atol(argv[4]);
  char *want = calloc(Emax + 1, 1);
  if (argc > 5) {
    FILE *f = fopen(argv[5], "r"); long e;
    while (fscanf(f, "%ld", &e) == 1) if (e >= 1 && e <= Emax) want[e] = 1;
    fclose(f);
  } else memset(want + 1, 1, Emax);
  /* primes up to B */
  char *comp = calloc(B + 1, 1); long np = 0;
  long *pr = malloc(sizeof(long) * (B / 2 + 10));
  for (long i = 2; i <= B; i++) if (!comp[i]) { pr[np++] = i; for (long j = i * i; j <= B; j += i) comp[j] = 1; }
  /* sieve: fac[e] = smallest prime p <= B with p | N(e) and N(e) != p */
  unsigned long *fac = calloc(Emax + 1, sizeof(unsigned long));
  long cnt_small = 0;
  #pragma omp parallel for schedule(dynamic, 64)
  for (long i = 0; i < np; i++) {
    unsigned long p = pr[i];
    unsigned long cm = ((C % (long)p) + p) % p, sm = ((S % (long)p) + p) % p;
    unsigned long x = 1; /* 2^e mod p, starting e=0 */
    long first = -1, ord = -1;
    for (long e = 1; e <= Emax; e++) {
      x = (x * 2) % p;
      if ((mulmod(cm, x, p) + sm) % p == 0) { if (first < 0) first = e; }
      if (x == 1) { ord = e; break; }
    }
    if (first < 0) continue;
    long step = ord > 0 ? ord : Emax + 1;
    for (long e = first; e <= Emax; e += step) {
      if (!want[e]) continue;
      /* N(e) == p is possible only for tiny e: skip if N(e) fits and equals p */
      if (e < 60) { unsigned __int128 v = (unsigned __int128)C << e; v = S >= 0 ? v + S : v - (unsigned long)(-S); if (v == p) continue; }
      unsigned long old;
      do { old = fac[e]; if (old && old <= p) break; } while (!__sync_bool_compare_and_swap(&fac[e], old, p));
    }
  }
  long *todo = malloc(sizeof(long) * (Emax + 1)); long nt = 0;
  for (long e = 1; e <= Emax; e++) if (want[e] && !fac[e]) todo[nt++] = e;
  fprintf(stderr, "sieved; %ld candidates need a pow test\n", nt);
  char *st = calloc(Emax + 1, 1); long *wit = calloc(Emax + 1, sizeof(long));
  long done = 0;
  #pragma omp parallel for schedule(dynamic, 1)
  for (long t = nt - 1; t >= 0; t--) {
    long e = todo[t];
    mpz_t N, Nm1, h, r, a, one, mone;
    __gmpz_init(N); __gmpz_init(Nm1); __gmpz_init(h); __gmpz_init(r); __gmpz_init(a); __gmpz_init(one); __gmpz_init(mone);
    buildN(N, e); __gmpz_sub_ui(Nm1, N, 1); __gmpz_set_ui(one, 1); __gmpz_set_ui(a, 3);
    __gmpz_powm(r, a, Nm1, N);
    if (__gmpz_cmp(r, one) != 0) { st[e] = 'C'; }
    else if (S != 1) { st[e] = 'Q'; }
    else {
      __gmpz_fdiv_q_2exp(h, Nm1, 1);
      st[e] = 'X';
      for (long q = 2; q < 1000; q++) {
        __gmpz_set_ui(a, q);
        if (__gmpz_jacobi(a, N) != -1) continue;
        __gmpz_powm(r, a, h, N);
        if (__gmpz_cmp(r, Nm1) == 0) { st[e] = 'P'; wit[e] = q; }
        break; /* a QNR either proves primality or (with Euler) proves compositeness */
      }
    }
    __gmpz_clear(N); __gmpz_clear(Nm1); __gmpz_clear(h); __gmpz_clear(r); __gmpz_clear(a); __gmpz_clear(one); __gmpz_clear(mone);
    long d = __sync_add_and_fetch(&done, 1);
    if (d % 200 == 0) fprintf(stderr, "%ld/%ld\n", d, nt);
  }
  for (long e = 1; e <= Emax; e++) {
    if (!want[e]) continue;
    if (fac[e]) printf("%ld F %lu\n", e, fac[e]);
    else if (st[e] == 'C') printf("%ld C fermat3-fail\n", e);
    else if (st[e] == 'P') printf("%ld P %ld\n", e, wit[e]);
    else printf("%ld %c\n", e, st[e]);
  }
  return 0;
}
