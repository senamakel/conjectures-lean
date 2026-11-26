/* Representation search for Sun 3.27-type statements:
 *   n = k + m, k,m >= 1, with  c*2^e + s  prime,  e = phi(k)/A + phi(m)/B.
 * Reading "sum":    e must be an integer (phi(k)*B + phi(m)*A divisible by A*B).
 *                   This is how Mathematica evaluates 2^(phi(k)/2+phi(m)/8): a
 *                   non-integer exponent gives a non-integer, hence "not prime".
 * Reading "strict": A | phi(k) and B | phi(m) separately.
 * Primality of N(e) comes from a status file written by ./scan (lines "e P a" are
 * Proth-proved primes; "F"/"C" are proved composites). Any other status, or an e
 * missing from the file, is reported as an error.
 *
 * usage: reps A B status nlo nhi sum|strict witness-out   (scan n in [nlo,nhi])
 *        reps A B status n n sum|strict -   with nlo==nhi also prints the distinct e
 * build: gcc -O2 -fopenmp reps.c -o reps
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage\n"); return 1; }
  long A = atol(argv[1]), B = atol(argv[2]);
  long nlo = atol(argv[4]), nhi = atol(argv[5]);
  int strict = strcmp(argv[6], "strict") == 0;
  long Emax = 0;
  /* status */
  FILE *f = fopen(argv[3], "r");
  long cap = 1 << 22; char *st = calloc(cap, 1); long *wit = calloc(cap, sizeof(long));
  long e; char c; char rest[256];
  while (fscanf(f, "%ld %c %255s", &e, &c, rest) >= 2) { st[e] = c; wit[e] = atol(rest); if (e > Emax) Emax = e; }
  fclose(f);
  /* totients */
  long L = nhi + 1; long *phi = malloc(sizeof(long) * (L + 1));
  for (long i = 0; i <= L; i++) phi[i] = i;
  for (long i = 2; i <= L; i++) if (phi[i] == i) for (long j = i; j <= L; j += i) phi[j] -= phi[j] / i;
  FILE *w = strcmp(argv[7], "-") ? fopen(argv[7], "w") : NULL;
  long fails = 0, errors = 0;
  for (long n = nlo; n <= nhi; n++) {
    long found = 0; char *seen = NULL;
    if (nlo == nhi) seen = calloc(cap, 1);
    for (long k = 1; k < n; k++) {
      long m = n - k, num;
      if (strict) { if (phi[k] % A || phi[m] % B) continue; num = phi[k] / A + phi[m] / B; }
      else { long t = phi[k] * B + phi[m] * A; if (t % (A * B)) continue; num = t / (A * B); }
      if (num > Emax || (st[num] != 'P' && st[num] != 'F' && st[num] != 'C')) {
        fprintf(stderr, "n=%ld k=%ld: exponent %ld not classified\n", n, k, num); errors++; continue; }
      if (seen) seen[num] = 1;
      if (st[num] == 'P') { if (w) fprintf(w, "%ld %ld %ld %ld %ld\n", n, k, m, num, wit[num]); found = 1; if (!seen) break; }
    }
    if (seen) {
      long cntd = 0, maxe = 0;
      for (long x = 0; x < cap; x++) if (seen[x]) { printf("%ld %c %ld\n", x, st[x], wit[x]); cntd++; maxe = x; }
      fprintf(stderr, "n=%ld: %ld distinct exponents, max %ld, representation %s\n", n, cntd, maxe, found ? "FOUND" : "NONE");
    }
    if (!found) { fails++; if (!seen) printf("NO REPRESENTATION: n=%ld\n", n); }
  }
  if (w) fclose(w);
  fprintf(stderr, "range %ld..%ld (%s): %ld without representation, %ld unclassified exponents\n", nlo, nhi, strict ? "strict" : "sum", fails, errors);
  return 0;
}
