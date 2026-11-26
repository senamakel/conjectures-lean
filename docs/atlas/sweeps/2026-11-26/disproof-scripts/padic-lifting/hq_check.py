import sys
from fractions import Fraction
from math import comb
from functools import lru_cache

def bernoulli_list(L):
    B = [Fraction(0)] * (L + 1)
    B[0] = Fraction(1)
    for m in range(1, L + 1):
        B[m] = -sum(comb(m + 1, j) * B[j] for j in range(m)) / (m + 1)
    return B

def vp(x, p):
    if x == 0: return 10**9
    x = abs(x); v = 0
    while x % p == 0: x //= p; v += 1
    return v

def vpq(fr, p):
    return vp(fr.numerator, p) - vp(fr.denominator, p)

BL = bernoulli_list(400)

def pred(p, a, n, k):
    eps = k & 1
    if (k - eps) % (p - 1) == 0:
        T = -1 - vp(k // 2, p)
    else:
        r = k % (p - 1)
        T = vpq(BL[2 * (r // 2)], p)
    return n + (n + vp(k, p)) * eps + T

E = int(sys.argv[1])
bad = 0; tot = 0
for line in sys.stdin:
    p, a, n, k, v = map(int, line.split())
    pr = pred(p, a, n, k)
    tot += 1
    if v != pr:
        bad += 1
        if bad <= 60:
            print("MISMATCH p=%d a=%d n=%d k=%d got=%s pred=%d  <k>=%d" % (p, a, n, k, (">=%d" % v) if v >= E else v, pr, k % (p - 1)))
print("total", tot, "mismatches", bad)
