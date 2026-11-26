# Generate block certificates (K', j, m, p) satisfying exactly the Lean checker's conditions.
import sys, math
from math import comb, isqrt
CN, CD = 5, 1
AN, AD = 693147, 10**6        # a < log 2
BN, BD = 6931472, 10**7       # b > log 2
BETAN, BETAD = 13, 4
def mkpi(N):
    sv = bytearray([1]) * (N + 1); sv[0] = sv[1] = 0
    for i in range(2, isqrt(N) + 1):
        if sv[i]: sv[i*i::i] = bytearray(len(sv[i*i::i]))
    PI = [0] * (N + 1); c = 0
    for i in range(N + 1): c += sv[i]; PI[i] = c
    return PI
def Ka_of(q, k):
    N = CN * k * k * AN * AN; D = CD * q * q * AD * AD
    return (N + D - 1) // D, N, D          # ceil
def c4(q, m, Ka):
    # (m*b/q + beta)^2 <= Ka   <=>  (m*BN*BETAD + BETAN*q*BD)^2 <= Ka*(q*BD*BETAD)^2
    return (m * BN * BETAD + BETAN * q * BD) ** 2 <= Ka * (q * BD * BETAD) ** 2
def cert(q, k, PI, X, cheb_only):
    Ka, N, D = Ka_of(q, k)
    assert (Ka - 1) * D < N
    if Ka < 17: return None
    m = 0
    while c4(q, m + 1, Ka): m += 1
    target = 2 ** (k + 1)
    cands = []
    if cheb_only:
        s = Ka.bit_length() - 1
        while s >= 3:
            cands.append((1 << s, -((-(1 << s)) // s), s)); s -= 1
    else:
        for Kp in range(min(Ka, X), 1, -1): cands.append((Kp, PI[Kp], None))
    for Kp, p, s in cands:
        j = 0
        while Kp ** ((j + 1) * q) <= 2 ** m: j += 1
        if j and p >= j and comb(p, j) ** q >= target:
            return (Kp, j, m, p)
    return None
if __name__ == '__main__':
    PI = mkpi(1024)
    out8 = []
    for k in range(88, 336):
        c = cert(8, k, PI, 1024, False)
        assert c, k
        out8.append(c)
    out1 = []
    for k in range(42, int(sys.argv[1])):
        c = cert(1, k, PI, 1024, True)
        assert c, k
        out1.append(c)
    print('q8 blocks', len(out8), 'max Kp', max(c[0] for c in out8))
    print('q1 blocks', len(out1), 'Kp range', min(c[0] for c in out1), max(c[0] for c in out1), 'max j', max(c[1] for c in out1))
    import json
    json.dump({'q8': out8, 'q1': out1}, open('certs.json', 'w'))
