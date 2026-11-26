# Independent implementation: s(N, N-k) = [y^k] prod_{i=1}^{N-1} (1 + i y), computed by a
# FLINT product tree over Z/p^E, truncated at degree K.  usage: hq_flint.py p N E K k1 k2 ...
import sys, flint, time
p, N, E, K = map(int, sys.argv[1:5]); ks = [int(x) for x in sys.argv[5:]]
M = p**E
ctx = flint.fmpz_mod_poly_ctx(M)
t0 = time.time()
def tree(lo, hi):  # product of (1 + i y) for lo <= i < hi, truncated to degree K
    if hi - lo <= 32:
        P = ctx([1])
        for i in range(lo, hi):
            P = (P * ctx([1, i % M]))
        return P
    mid = (lo + hi) // 2
    A = tree(lo, mid); B = tree(mid, hi)
    C = A * B
    if C.degree() > K:
        C = ctx([C[j] for j in range(K + 1)])
    return C
P = tree(1, N)
def vp(x):
    x = int(x)
    if x == 0: return ">=%d" % E
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
for k in ks:
    print("p=%d N=%d k=%d v=%s" % (p, N, k, vp(P[k])))
print("time %.1fs" % (time.time() - t0), file=sys.stderr)
