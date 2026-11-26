"""Second route: direct incidence-algebra computation of P, Q, Z, Y (and chi) on the explicit
lattice of flats of M_{3,2} built in explicit_k3.py; compared with the composition-algebra values."""
import sys
sys.argv = [sys.argv[0], sys.argv[1] if len(sys.argv) > 1 else "2"]
import explicit_k3 as E
from flint import fmpz_poly
from invs import build, evaluate
from flags import coalescence_alpha

T = fmpz_poly([0, 1]); ONE = fmpz_poly([1]); ZERO = fmpz_poly([])
els = [(0, 0)] + [(1, a) for a in E.atoms] + [(2, L) for L in E.rank2] + [(3, H) for H in E.hyp] + [(4, (1 << E.nel) - 1)]
N = len(els)
rk = [r for r, m in els]
mask = [m for r, m in els]
# up[i] = list of j >= i
up = [[] for _ in range(N)]
for i in range(N):
    for j in range(N):
        if rk[j] >= rk[i] and (mask[i] & mask[j]) == mask[i]:
            if rk[j] > rk[i] or i == j:
                up[i].append(j)
print("elements", N, "comparable pairs", sum(len(u) for u in up))
upset = [set(u) for u in up]
order = sorted(range(N), key=lambda i: rk[i])
# Mobius mu(i,j) via mu(i,j) = -sum_{i<=k<j} mu(i,k)
mu = {}
for i in range(N):
    for j in sorted(up[i], key=lambda j: rk[j]):
        if j == i:
            mu[i, j] = 1
        else:
            mu[i, j] = -sum(mu[i, k] for k in up[i] if rk[k] < rk[j] and j in upset[k])
def interval(i, j):
    return [k for k in up[i] if j in upset[k]]
chi = {}
for (i, j), m in list(mu.items()):
    pass
for i in range(N):
    for j in up[i]:
        s = ZERO
        for k in interval(i, j):
            s += mu[i, k] * T ** (rk[j] - rk[k])
        chi[i, j] = s
# P on all intervals: t^n P(1/t) - P(t) = sum_{i<k<=j} chi(i,k) P(k,j)
P = {}
for i in sorted(range(N), key=lambda i: -rk[i]):
    for j in sorted(up[i], key=lambda j: rk[j]):
        n = rk[j] - rk[i]
        if n == 0:
            P[i, j] = ONE; continue
        R = ZERO
        for k in interval(i, j):
            if k != i:
                R += chi[i, k] * P[k, j]
        co = [int(x) for x in R.coeffs()] + [0] * (n + 2)
        assert all(co[a] == -co[n - a] for a in range(n + 1))
        P[i, j] = fmpz_poly([-co[a] for a in range(n + 1) if 2 * a < n])
# Q: sum_{i<=k<=j} (-1)^{rk(i,k)} P(i,k) Q(k,j) = delta
Q = {}
for i in sorted(range(N), key=lambda i: -rk[i]):
    for j in sorted(up[i], key=lambda j: rk[j]):
        if i == j:
            Q[i, j] = ONE; continue
        s = ZERO
        for k in interval(i, j):
            if k != i:
                s += (-1) ** (rk[k] - rk[i]) * P[i, k] * Q[k, j]
        Q[i, j] = -s
top = N - 1; bot = 0; r = 4
Z = ZERO; Yh = ZERO
for k in range(N):
    Z += T ** rk[k] * P[k, top]
    Yh += (-1) ** rk[k] * Q[bot, k] * T ** (r - rk[k]) * mu[k, top]
Y = Yh if r % 2 == 0 else -Yh
direct = dict(chi=chi[bot, top], P=P[bot, top], Q=Q[bot, top], Z=Z, Y=Y)
I = build(5)
al = coalescence_alpha(3, E.q)
for name, val in direct.items():
    other = evaluate(I[name], al, 4)
    print(name, val, "|| composition algebra:", other, "AGREE" if val == other else "DISAGREE")
