import sys, os
# writes spec files for hs.c into the given directory
LIM = 1 << 44
def pw(b):
    out, x = [], 1
    while x < LIM:
        out.append(x); x *= b
    return out
def pairs(A, B, ordered_le=False):
    s = set()
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            if ordered_le and j < i: continue
            if a + b < LIM: s.add(a + b)
    return s
def prods(A, B):
    return {a * b for a in A for b in B if a * b < LIM}
def catalan():
    out, c, k = [], 1, 0
    while c < LIM:
        if k > 0: out.append(c)
        c = c * 2 * (2 * k + 1) // (k + 2); k += 1
    return out
def bell():
    row, out = [1], [1]  # Bell(0)=1
    while True:
        new = [row[-1]]
        for v in row: new.append(new[-1] + v)
        row = new
        if row[0] >= LIM: break
        out.append(row[0])
    return out[1:]  # Bell(k), k >= 1
P2, P3, P4, P5 = pw(2), pw(3), pw(4), pw(5)
SQ = (1, 0, 1, 0); TWO = (2, 0, 1, 0); TRI = (1, 1, 2, 1)
PENT = (3, -1, 2, 1); HEXm = (2, -1, 1, 1); HEXp = (2, 1, 1, 1)
OCTZ = (3, -2, 1, 0); OCTpZ = (3, 2, 1, 0); OCTpN = (3, 2, 1, 1)
S = {}
S['a302984'] = (SQ, TWO, (2, 1, 0), pairs(P2, [5 * x for x in P2]))
S['a303338'] = (SQ, TWO, (2, 1, 0), pairs([3 * x for x in P2], P4))
S['a303637'] = (SQ, SQ, (1, 1, 0), pairs(P2, [5 * x for x in P2]))
S['a302983'] = (SQ, TWO, (2, 1, 0), pairs(P2, [3 * x for x in P2]))
S['a303401'] = (PENT, PENT, (0, 1, 0), pairs(P3, P3, True))
S['a303432c1'] = (HEXm, HEXm, (0, 1, 0), pairs(P2, P2, True))
S['a303432c2'] = (HEXp, HEXp, (0, 1, 0), pairs(P2, P2, True))
S['a303432c3'] = (HEXm, HEXp, (0, 1, 0), pairs(P2, P2, True))
S['a303428'] = (OCTZ, OCTZ, (0, 1, 0), pairs(P3, P3, True))
S['a303428m'] = (OCTpZ, OCTpN, (0, 1, 0), pairs(P3, P3, True))
S['a308566'] = (TRI, TRI, (1, 4, 1), prods(P4, P5))
S['a308584'] = (TRI, TRI, (1, 4, 1), prods(P5, pw(8)))
S['a308621'] = (TRI, TRI, (1, 4, 1), prods(P2, pw(125)))
S['a308623'] = (TRI, TRI, (1, 4, 1), prods(P2, pw(100)))
S['a303389'] = (TRI, TRI, (1, 4, 1), pairs(P5, P5, True))
S['a303363'] = (TRI, TRI, (1, 4, 1), {2**c + 2**d for c in range(0, 45, 2) for d in range(c, 45) if 2**c + 2**d < LIM})
S['a303233'] = (TRI, TRI, (1, 4, 1), pairs(P2, P2, True))
S['a303543'] = (SQ, SQ, (1, 1, 0), pairs(catalan(), catalan(), True))
S['a303601'] = (TRI, TRI, (1, 4, 1), pairs(bell(), bell(), True))
S['a308934c1'] = (SQ, TWO, (2, 1, 0), pairs([x * x for x in prods(P2, P3)], [x * x for x in prods(P2, P3)]))
S['a308934c2'] = (SQ, TWO, (2, 1, 0), pairs([x * x for x in prods(P2, P3)], [x * x for x in prods(P2, P5)]))
d = sys.argv[1]; K = int(sys.argv[2]) if len(sys.argv) > 2 else 4
for k, (Fp, Gp, (mode, A, B), sp) in S.items():
    sp = sorted(sp)
    with open(os.path.join(d, k + '.spec'), 'w') as f:
        f.write('%d %d %d %d\n%d %d %d %d\n%d %d %d\n%d\n%d\n' % (Fp + Gp + (mode, A, B, K, len(sp))))
        f.write(' '.join(map(str, sp)) + '\n')
    print(k, len(sp), 'values; <=1e10:', sum(1 for x in sp if x <= 10**10), '<=1e12:', sum(1 for x in sp if x <= 10**12))
# validation-only specs (facts quoted in the OEIS entries)
V = {}
V['v_oct2'] = (OCTZ, OCTZ, (0, 1, 0), pairs(P2, P2, True))          # 76683391 least failure (A303428 comment)
V['v_bellsq'] = (SQ, SQ, (1, 1, 0), pairs(bell(), bell(), True))     # 111277 fails (A303601 comment)
V['v_250'] = (TRI, TRI, (1, 4, 1), prods(P2, pw(250)))               # 7272774228 fails (A308621 comment)
V['v_23'] = (TRI, TRI, (1, 4, 1), prods(P2, P3))                     # 729546026 fails (A308623 comment)
for k, (Fp, Gp, (mode, A, B), sp) in V.items():
    sp = sorted(sp)
    with open(os.path.join(d, k + '.spec'), 'w') as f:
        f.write('%d %d %d %d\n%d %d %d %d\n%d %d %d\n%d\n%d\n' % (Fp + Gp + (mode, A, B, K, len(sp))))
        f.write(' '.join(map(str, sp)) + '\n')
# A308661: Conj 2 on N = 24n+10 (squares + (2^c 3^d)^2, d >= 1); Conj 1 on N = 3n+1 (T+T + (2^c 5^d)^2)
W = {}
W['a308661c2'] = (SQ, SQ, (1, 1, 0), {(x * 3) ** 2 for x in prods(P2, P3) if (3 * x) ** 2 < LIM})
W['a308661c1'] = (TRI, TRI, (1, 4, 1), {x * x for x in prods(P2, P5) if x * x < LIM})
for k, (Fp, Gp, (mode, A, B), sp) in W.items():
    sp = sorted(sp)
    with open(os.path.join(d, k + '.spec'), 'w') as f:
        f.write('%d %d %d %d\n%d %d %d %d\n%d %d %d\n%d\n%d\n' % (Fp + Gp + (mode, A, B, K, len(sp))))
        f.write(' '.join(map(str, sp)) + '\n')
    print(k, len(sp))
