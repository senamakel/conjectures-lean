import numpy as np, sys
from math import comb
def series(M, N):
    # b_M(0..N) mod 2^64 via H_M(x) = H_M(x^2) / (1-x)^M
    if N == 0: return np.ones(1, dtype=np.uint64)
    half = series(M, N//2)
    a = np.zeros(N+1, dtype=np.uint64); a[0:2*len(half):2] = half[: (N//2)+1][: len(a[0::2])]
    for _ in range(M): a = np.cumsum(a, dtype=np.uint64)
    return a
def bigint(M, N):
    # independent: product over powers of two of 1/(1-x^p), M times, exact Python ints
    a = [0]*(N+1); a[0] = 1
    p = 1
    while p <= N:
        for _ in range(M):
            for i in range(p, N+1): a[i] += a[i-p]
        p *= 2
    return a
def v2(x):
    x = int(x)
    if x == 0: return 64
    return (x & -x).bit_length()-1
if __name__ == '__main__':
    # cross-check
    for M in (1,3,7,15):
        B = bigint(M, 600); s = series(M, 600)
        assert all(int(s[i]) == B[i] % 2**64 for i in range(601)), M
    print("b1(4),b1(16):", bigint(1,16)[4], bigint(1,16)[16], " b7(64)-b7(16):", bigint(7,64)[64]-bigint(7,64)[16])
    KMAX = int(sys.argv[1]); NMAX = int(sys.argv[2])
    N = 2**(KMAX+1)*NMAX
    for m in range(1,7):
        M = 2**m-1; b = series(M, N)
        print(f"m={m} M={M}")
        for k in range(m+2, KMAX+1):
            req = 4*((k+1)//2)-2
            vals = [min(v2(np.uint64(b[2**(k+1)*n]) - np.uint64(b[2**(k-1)*n])), 64) for n in range(1, NMAX+1)]
            odd = [vals[n-1] for n in range(1, NMAX+1, 2)]
            fails = sum(1 for x in vals if x < req)
            print(f"  k={k:2d} req={req:2d} min_v2(all n)={min(vals):2d} min_v2(odd n)={min(odd):2d} max_odd={max(odd):2d} n=1:{vals[0]:2d} fails={fails}/{NMAX}")
