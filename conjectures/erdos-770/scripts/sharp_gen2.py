# Certificates for Erdos770/Sharp/Certs*.lean; conditions identical to `blockOK` and `piOK`.
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from sharp_gen import Ka_of, c4, mkpi
from math import comb
PI = mkpi(1024)
def tryK(q, k, Kp, p, m):
    j = 0
    while Kp ** ((j + 1) * q) <= 2 ** m: j += 1
    if j and comb(p, j) ** q >= 2 ** (k + 1): return j
def cert(q, k):
    Ka, N, D = Ka_of(q, k)
    assert (Ka - 1) * D < N and Ka >= 17
    m = 0
    while c4(q, m + 1, Ka): m += 1
    s = Ka.bit_length() - 1
    while s >= 3:
        Kp = 1 << s; p = Kp // s
        if Kp <= Ka:
            j = tryK(q, k, Kp, p, m)
            if j: return (Kp, j, m, p)
        s -= 1
    for Kp in range(min(Ka, 1024), 1, -1):
        j = tryK(q, k, Kp, PI[Kp], m)
        if j: return (Kp, j, m, PI[Kp])
    raise Exception(k)
def lean_list(name, cs, k0, q, doc):
    out = [f'/-- {doc} -/', f'def {name} : List (ℕ × ℕ × ℕ × ℕ) := [']
    out.append(',\n'.join(f'  ({a}, {b}, {c}, {d})' for (a, b, c, d) in cs) + ']')
    return '\n'.join(out)
if __name__ == '__main__':
    c8 = [cert(8, k) for k in range(88, 336)]
    c1 = [cert(1, k) for k in range(42, 709)]
    print('exact-pi certs in c8:', sum(1 for c in c8 if c[0] & (c[0] - 1)), 'max m', max(c[2] for c in c1))
    open('certs8.lean.txt', 'w').write(lean_list('certs8', c8, 88, 8, 'Blocks `2^k ≤ n⁸ < 2^(k+1)` for `k = 88, …, 335` (`2¹¹ ≤ n < 2⁴²`).'))
    open('certs1.lean.txt', 'w').write(lean_list('certs1', c1, 42, 1, 'Blocks `2^k ≤ n < 2^(k+1)` for `k = 42, …, 708`.'))
