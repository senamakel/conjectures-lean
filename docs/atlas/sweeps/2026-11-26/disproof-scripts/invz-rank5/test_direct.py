"""Sanity checks of lattice.invZ against published formulas."""
from math import comb
from lattice import Lattice

def uniform(k, n):
    return Lattice(n, lambda S: min(bin(S).count('1'), k))

def grx_uniform(k, n):
    # Gao-Ruan-Xie Thm 1.1
    y = [0] * (k + 1)
    for i in range(k // 2 + 1):
        y[i] += comb(n, i) * comb(n - i - 1, n - k)
    for i in range((k - 1) // 2 + 1):
        y[k - i] += comb(n, i) * comb(n - i - 1, n - k)
    return y

ok = True
for k in range(1, 6):
    for n in range(k, 9):
        L = uniform(k, n)
        Y, P, Q = L.invZ()
        if Y != grx_uniform(k, n):
            ok = False; print('MISMATCH', k, n, Y, grx_uniform(k, n))
        if any(c < 0 for c in Q) or any(c < 0 for c in P):
            ok = False; print('negative P/Q', k, n, P, Q)
print('uniform U_{k,n}, k<=5, n<=8 vs GRX Thm 1.1:', ok)
print('Q(U_{2,5}) =', uniform(2, 5).invZ()[2], '(expect [4])')
print('Y(B_5) =', uniform(5, 5).invZ()[0], '(expect (1+t)^5)')
