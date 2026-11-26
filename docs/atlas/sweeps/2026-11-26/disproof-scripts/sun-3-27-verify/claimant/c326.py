"""Sun, arXiv:1211.1588 Conjecture 3.26.
(i)  n > 5: n = k + m, k, m >= 3, 2^phi(k) + 2^phi(m) - 1 prime        (mode i, base 2)
(ii) n > N(a): n = k + m, 2 < k < n-2, a^phi(k) + a^(phi(m)/2) - 1 prime (mode ii, base a)
For each n, search pairs in increasing size, sieve by small primes, PRP test (base 3 strong);
report n with no PRP (then each value needs a compositeness proof) and the count of PRPs
among the first few hits (mode full counts all).
usage: python3 c326.py mode a n0 n1 workers [full]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pylib'))
import gmpy2
from multiprocessing import Pool

mode, a, n0, n1, W = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
full = len(sys.argv) > 6
NMAX = n1 + 1
phi = list(range(NMAX))
for i in range(2, NMAX):
    if phi[i] == i:
        for j in range(i, NMAX, i):
            phi[j] -= phi[j] // i
SP = [p for p in range(3, 2000) if all(p % q for q in range(2, int(p**0.5) + 1)) and a % p]
POW = {p: [pow(a, x, p) for x in range(p - 1)] for p in SP}  # a^x mod p, period divides p-1

def exps(n, k):
    m = n - k
    if mode == 'i':
        return phi[k], phi[m]
    if phi[m] % 2:
        return None
    return phi[k], phi[m] // 2

def work(n):
    if mode == 'i':
        ks = range(3, n // 2 + 1)
    else:
        ks = range(3, n - 2)
    seen = {}
    for k in ks:
        e = exps(n, k)
        if e is not None and e not in seen:
            seen[e] = k
    cand = sorted(seen, key=lambda e: max(e))
    cnt = 0; tests = 0
    for (x, y) in cand:
        ok = True
        for p in SP:
            t = p - 1
            if (POW[p][x % t] + POW[p][y % t] - 1) % p == 0:
                N = gmpy2.mpz(a)**x + gmpy2.mpz(a)**y - 1
                if N != p:
                    ok = False
                break
        if not ok:
            continue
        N = gmpy2.mpz(a)**x + gmpy2.mpz(a)**y - 1
        if N < 2:
            continue
        tests += 1
        if gmpy2.is_strong_prp(N, 3) if N > 3 else N in (2, 3):
            cnt += 1
            if not full and cnt >= 1:
                break
    return n, cnt, tests, len(cand)

if __name__ == '__main__':
    with Pool(W) as pool:
        for n, cnt, tests, nc in pool.imap(work, range(n0, n1 + 1), chunksize=4):
            if cnt == 0 or full:
                print(n, cnt, tests, nc, flush=True)
    print("done", mode, a, n0, n1, file=sys.stderr)
