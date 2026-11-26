"""Independent check: build the rank-4 coalescence matroid M_{3,q} explicitly (q prime here)
from its rank function, enumerate all flats by closure, count flags directly."""
import sys
from itertools import combinations, product
from flags import coalescence_alpha

q = int(sys.argv[1]) if len(sys.argv) > 1 else 2
k = 3
# GF(q^3) with an irreducible cubic: find one
def find_irred():
    for a, b, c in product(range(q), repeat=3):
        # x^3 + a x^2 + b x + c irreducible iff no root (degree 3)
        if all((x ** 3 + a * x * x + b * x + c) % q for x in range(q)):
            return (c, b, a)
irr = find_irred()

def fmul(u, v):
    # elements as tuples of 3 coeffs (low first)
    prod = [0] * 5
    for i in range(3):
        for j in range(3):
            prod[i + j] = (prod[i + j] + u[i] * v[j]) % q
    for d in (4, 3):
        co = prod[d]
        if co:
            prod[d] = 0
            for i in range(3):
                prod[d - 3 + i] = (prod[d - 3 + i] - co * irr[i]) % q
    return tuple(prod[:3])

def fadd(u, v):
    return tuple((a + b) % q for a, b in zip(u, v))

def fpow(u, e):
    r = (1, 0, 0)
    for _ in range(e):
        r = fmul(r, u)
    return r

K = list(product(range(q), repeat=3))
ZERO = (0, 0, 0)
# projective points of V = K+K (vectors in F_q^6), normalised: first nonzero coord = 1
def normalise(v):
    for x in v:
        if x:
            inv = pow(x, q - 2, q)
            return tuple((y * inv) % q for y in v)
    return None
pts = sorted({normalise(a + b) for a in K for b in K if (a + b) != (0,) * 6})
pidx = {p: i for i, p in enumerate(pts)}
npts = len(pts)
free = {a: npts + i for i, a in enumerate(K)}
nel = npts + len(K)
print("points", npts, "free", len(K))

# span closure for geometric points (as set of point indices) via Gaussian elimination
def rank_vecs(vs):
    rows = [list(v) for v in vs]
    r = 0
    ncol = 6
    for col in range(ncol):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][col] % q:
                piv = i; break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][col], q - 2, q)
        rows[r] = [(x * inv) % q for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] % q:
                f = rows[i][col]
                rows[i] = [(x - f * y) % q for x, y in zip(rows[i], rows[r])]
        r += 1
    return r

def span_points(vs):
    r = rank_vecs(vs)
    out = []
    for i, p in enumerate(pts):
        if rank_vecs(list(vs) + [p]) == r:
            out.append(i)
    return out

# blocks
blocks = []
for c0, c1, c2 in product(K, repeat=3):
    W = set()
    for t in K:
        if t == ZERO:
            continue
        ft = fadd(fadd(fmul(c0, t), fmul(c1, fpow(t, q))), fmul(c2, fpow(t, q * q)))
        W.add(pidx[normalise(t + ft)])
    mask = 0
    for i in W:
        mask |= 1 << i
    mask |= 1 << free[c2]
    blocks.append(mask)
print("blocks", len(blocks), len(set(blocks)))

def bits(mask):
    i = 0
    out = []
    while mask:
        if mask & 1:
            out.append(i)
        mask >>= 1; i += 1
    return out

def rankQ(S):
    g = [pts[i] for i in S if i < npts]
    f = sum(1 for i in S if i >= npts)
    return rank_vecs(g) + f

def closQ(S):
    g = [pts[i] for i in S if i < npts]
    m = 0
    for i in (span_points(g) if g else []):
        m |= 1 << i
    for i in S:
        if i >= npts:
            m |= 1 << i
    return m

# rank-1, rank-2 flats of M (= of Q, ranks <= k-1)
atoms = [1 << i for i in range(nel)]
rank2 = set()
for a, b in combinations(range(nel), 2):
    rank2.add(closQ([a, b]))
rank2 = list(rank2)
print("rank2 flats", len(rank2))
# hyperplanes of M: closures of independent 3-sets
hyp = set()
cnt = 0
for S in combinations(range(nel), 3):
    if rankQ(S) != 3:
        continue
    m = 0
    for i in S:
        m |= 1 << i
    inb = [B for B in blocks if B & m == m]
    assert len(inb) <= 1
    if inb:
        hyp.add(inb[0])
    else:
        hyp.add(closQ(S))
hyp = list(hyp)
print("hyperplanes", len(hyp))
pc = lambda m: bin(m).count("1")
alpha = {}
alpha[()] = 1
alpha[(1,)] = nel
alpha[(2,)] = len(rank2)
alpha[(3,)] = len(hyp)
alpha[(1, 2)] = sum(pc(L) for L in rank2)
alpha[(1, 3)] = sum(pc(H) for H in hyp)
a23 = 0; a123 = 0
for H in hyp:
    for L in rank2:
        if L & H == L:
            a23 += 1; a123 += pc(L)
alpha[(2, 3)] = a23
alpha[(1, 2, 3)] = a123
ref = coalescence_alpha(3, q)
for S in sorted(alpha, key=lambda s: (len(s), s)):
    print(S, alpha[S], ref[S], "OK" if alpha[S] == ref[S] else "MISMATCH")
