"""Independent check, from the definitions, that n has NO representation
n = k + m (k, m >= 1) with F(e) prime, e = phi(k)/a + phi(m)/b (exact rational, must be an integer).
phi from sympy.totient (not the C sieve); no OEIS list is used: every attainable integer e
gets a compositeness certificate (a prime factor < 2^20, else a failed Fermat test base 3,
which proves compositeness). Prints certificate stats; exits 1 if any F(e) is a probable prime.
usage: python3 verify.py a b form n [certfile]
forms: 3x2p1 (3*2^e+1), 3x2m1 (3*2^e-1), 2p3, 2m3, 2m5 (2^e+3, 2^e-3, 2^e-5), 2x3p1, 2x3m1 (2*3^e+-1)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pylib'))
import gmpy2
from fractions import Fraction
from sympy import totient, primerange

a, b, form, n = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
cert = open(sys.argv[5], 'w') if len(sys.argv) > 5 else None
F = {
 '3x2p1': lambda e: 3 * gmpy2.mpz(2)**e + 1, '3x2m1': lambda e: 3 * gmpy2.mpz(2)**e - 1,
 '2p3': lambda e: gmpy2.mpz(2)**e + 3, '2m3': lambda e: gmpy2.mpz(2)**e - 3,
 '2m5': lambda e: gmpy2.mpz(2)**e - 5,
 '2x3p1': lambda e: 2 * gmpy2.mpz(3)**e + 1, '2x3m1': lambda e: 2 * gmpy2.mpz(3)**e - 1,
}[form]
R = {  # F(e) mod p, computed without forming F(e)
 '3x2p1': lambda e,p: (3*pow(2,e,p)+1)%p, '3x2m1': lambda e,p: (3*pow(2,e,p)-1)%p,
 '2p3': lambda e,p: (pow(2,e,p)+3)%p, '2m3': lambda e,p: (pow(2,e,p)-3)%p,
 '2m5': lambda e,p: (pow(2,e,p)-5)%p,
 '2x3p1': lambda e,p: (2*pow(3,e,p)+1)%p, '2x3m1': lambda e,p: (2*pow(3,e,p)-1)%p,
}[form]
phi = [0] + [int(totient(i)) for i in range(1, n)]
E = {}
for k in range(1, n):
    x = Fraction(phi[k], a) + Fraction(phi[n - k], b)
    if x.denominator == 1:
        E.setdefault(int(x), k)
print(f"n={n}: {n-1} pairs, {len(E)} distinct integer exponents, range [{min(E)},{max(E)}]")
small = list(primerange(2, 1 << 20))

def certify(e):
    N = F(e)
    if N < 2:
        return e, 'trivial', None
    if N.bit_length() <= 40:
        if gmpy2.is_prime(N, 50):
            return e, 'PRIME', None
        return e, 'factor', int(next(p for p in small if N % p == 0 and N != p))
    for p in small:
        if R(e, p) == 0:
            assert N % p == 0
            return e, 'factor', p
    if gmpy2.powmod(3, N - 1, N) == 1:
        return e, 'PRP', None
    return e, 'fermat3', None

if __name__ == '__main__':
    from multiprocessing import Pool
    W = int(os.environ.get('W', '8'))
    nf = nfermat = 0
    with Pool(W) as pool:
        res = sorted(pool.imap_unordered(certify, sorted(E), chunksize=16))
    for e, kind, p in res:
        if kind in ('PRIME', 'PRP'):
            print("PROBABLE PRIME at e =", e, "k =", E[e], flush=True); sys.exit(1)
        if kind == 'factor': nf += 1
        if kind == 'fermat3': nfermat += 1
        if cert: cert.write(f"{e} {kind} {p if p else ''}\n")
    if cert: cert.close()
    print(f"all {len(E)} values composite: {nf} by small factor, {nfermat} by Fermat base 3", flush=True)
