# For primes q, find residues r mod q^2 whose solution set {k : F_k == r mod q^2} is periodic mod pi(q)
# (the "fixed" k with F_{k+pi} == F_k mod q^2). Output: q, pi(q), list of (r, [k mod pi]).
import sys, json
from sympy import primerange, factorint, divisors
def fibpair(n, m):  # (F_n, F_{n+1}) mod m
    if n == 0: return (0, 1 % m)
    a, b = fibpair(n >> 1, m)
    c = (a * ((2 * b - a) % m)) % m
    d = (a * a + b * b) % m
    return (d, (c + d) % m) if n & 1 else (c, d)
def pisano(q):
    if q == 2: return 3
    if q == 5: return 20
    base = q - 1 if q % 5 in (1, 4) else 2 * (q + 1)
    for d in sorted(divisors(base)):
        if fibpair(d, q) == (0, 1): return d
def seq(K, lucas=False):
    pass
B = int(sys.argv[1]); smooth = int(sys.argv[2]); lucas = len(sys.argv) > 3 and sys.argv[3] == 'L'
out = []
for q in primerange(2, B):
    P = pisano(q)
    if max(factorint(P)) > smooth: continue
    M = q * q
    # iterate k in [0, P): value and value at k+P
    a, b = (2 % M, 1) if lucas else (0, 1)     # G_0, G_1
    sa, sb = fibpair(P, M)                      # F_P, F_{P+1}
    groups = {}
    x, y = a, b
    for k in range(P):
        # G_{k+P} = G_k*F_{P+1} + G_{k-1}*F_P ; use G_{k+1}: G_{k+P} = G_{k+1}F_P + G_k F_{P-1}
        fpm1 = (sb - sa) % M
        shifted = (y * sa + x * fpm1) % M
        if shifted == x:
            groups.setdefault(x, []).append(k)
        x, y = y, (x + y) % M
    if groups:
        out.append((q, P, sorted(groups.items(), key=lambda t: -len(t[1]))))
for q, P, g in out:
    print(q, P, factorint(P), [(r, ks) for r, ks in g[:3]])
json.dump(out, open(f'fibsq_{"L" if lucas else "F"}_{B}_{smooth}.json', 'w'))
