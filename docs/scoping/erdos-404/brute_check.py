"""Independent brute-force check of cover.c on small cases.

Dense DP: the set of subset sums mod p^D as a Python big-int bitset, elements
(N+j)!/N! for 0 <= j < H, modulus p^{v_p((N+H)!/N!)}. Also the tail mode:
elements n! for nmin <= n with v_p(n!) < D, modulus p^D, reports whether -1 is hit.
Usage: python3 brute_check.py block p N H | tail p D nmin
"""
import sys


def vp(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def sumset_bits(elts, M):
    mask = (1 << M) - 1
    S = 1
    for e in elts:
        e %= M
        S |= ((S << e) | (S >> (M - e))) & mask
    return S


def main():
    mode = sys.argv[1]
    p = int(sys.argv[2])
    if mode == "block":
        N, H = int(sys.argv[3]), int(sys.argv[4])
        D = sum(vp(N + i, p) for i in range(1, H + 1))
        M = p ** D
        elts, x = [], 1
        for j in range(H):
            if j:
                x *= N + j
            elts.append(x % M)
        S = sumset_bits(elts, M)
        print(f"BRUTE block p={p} N={N} H={H} D={D} covered={bin(S).count('1')}/{M}")
    else:
        D, nmin = int(sys.argv[3]), int(sys.argv[4])
        M = p ** D
        elts, f, n = [], 1, 0
        while True:
            if n:
                f *= n
            if vp(f, p) >= D if f else False:
                break
            if n >= nmin:
                elts.append(f % M)
            n += 1
        S = sumset_bits(elts, M)
        print(f"BRUTE tail p={p} D={D} nmin={nmin} covered={bin(S).count('1')}/{M} "
              f"minus1={(S >> (M - 1)) & 1}")


if __name__ == "__main__":
    main()
