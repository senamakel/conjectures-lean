import sys
from math import comb, factorial
from functools import lru_cache

def v2(x):
    x = abs(x)
    return (x & -x).bit_length() - 1 if x else 10**9

def s2(x): return bin(x).count('1')

def S(n, k):
    t = 0
    for j in range(k + 1):
        term = comb(k, j) * pow(j, n)
        t += -term if (k - j) & 1 else term
    q, r = divmod(t, factorial(k))
    assert r == 0
    return q

def f(b, c): return s2(b) - s2(c) + v2(comb(2*c - b - 1, c))

H = int(sys.argv[1]); CMAX = int(sys.argv[2])
for h in range(3, H + 1):
    for c in range(2, CMAX + 1):
        for b in range(1, c):
            for a in range(3, 2**(h-1) + 1, 4):
                n = c * 2**h + 2; k = b * 2**h + a
                got = v2(S(n, k))
                pred = s2(a) + f(b, c) + v2(comb(a + 1, 2)) - 1
                cond = 2**(h-2) >= v2(comb(2*c-b-1, c))
                if got != pred:
                    print("FAIL h=%d c=%d b=%d a=%d n=%d k=%d got=%d pred=%d cond=%s" % (h, c, b, a, n, k, got, pred, cond), flush=True)
    print("done h", h, flush=True)
