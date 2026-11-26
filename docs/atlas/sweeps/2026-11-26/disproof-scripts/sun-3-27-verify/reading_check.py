"""Which reading of the rational exponent reproduces Sun's OEIS data?

A234451 counts n = k + m with 2^(phi(k)/2 + phi(m)/6) + 3 prime (part (i) of 3.27);
A234504 counts 2^(phi(k) + phi(m)/4) - 5 prime (part (iv)).
Both use Mathematica, where 2^(r) for a non-integer rational r is not an integer and
so PrimeQ is False; an integral sum such as 1/2 + 1/2 evaluates to an integer.
Pure Python, exact arithmetic; deterministic Miller-Rabin for n < 3.3e24 and a
strong-PRP test (bases = first 20 primes) above that, which is ample for a
reading test on n <= 84.
"""
from fractions import Fraction
from math import gcd

def phi(n):
    r, x, p = n, n, 2
    while p * p <= x:
        if x % p == 0:
            while x % p == 0:
                x //= p
            r -= r // p
        p += 1
    if x > 1:
        r -= r // x
    return r

BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

def is_prime(n):
    if n < 2:
        return False
    for p in BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def count(n, A, B, c, s, reading):
    tot = 0
    for k in range(1, n):
        m = n - k
        if reading == "strict":
            if phi(k) % A or phi(m) % B:
                continue
        e = Fraction(phi(k), A) + Fraction(phi(m), B)
        if e.denominator != 1:
            continue
        if is_prime(c * 2 ** int(e) + s):
            tot += 1
    return tot

A234451 = [0,0,0,0,0,0,0,0,0,1,1,2,2,2,2,3,4,4,4,3,5,4,5,4,6,4,4,5,5,5,6,6,6,5,6,8,7,6,5,7,8,7,10,6,7,9,7,5,5,8,6,6,7,9,3,7,10,9,3,8,6,8,6,9,9,12,5,8,8,10,9,10,9,8,8,8,10,9,12,10,13,11,9,10]
A234504 = [0,0,0,0,0,0,0,1,1,0,2,1,1,3,2,3,2,3,2,3,4,5,5,4,5,6,7,4,5,6,7,6,5,7,8,5,7,9,8,8,6,8,7,10,7,10,10,9,9,8,9,10,5,10,10,9,10,10,9,10,9,7,12,14,10,9,5,11,7,13,8,13,6,9,11,11,14,15,9,13]

for name, data, A, B, c, s in [("A234451", A234451, 2, 6, 1, 3), ("A234504", A234504, 1, 4, 1, -5)]:
    for reading in ("sum", "strict"):
        got = [count(n, A, B, c, s, reading) for n in range(1, len(data) + 1)]
        bad = [n for n in range(1, len(data) + 1) if got[n - 1] != data[n - 1]]
        print(name, reading, "matches all" if not bad else f"mismatch at n={bad[:10]}")

# Part (ii) forms: report the small-n behaviour and the threshold in each reading
for A, B, thr in [(2, 8, 25), (2, 12, 38)]:
    for reading in ("sum", "strict"):
        zeros = [n for n in range(2, 400) if count(n, A, B, 3, 1, reading) == 0]
        print(f"3*2^(phi(k)/{A}+phi(m)/{B})+1, {reading}: n<400 with no representation: {zeros}")
