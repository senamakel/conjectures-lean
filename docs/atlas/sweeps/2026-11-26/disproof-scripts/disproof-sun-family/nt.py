import math, random
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
def rho(n):
    if n % 2 == 0: return 2
    while True:
        x = y = random.randrange(2, n); c = random.randrange(1, n); d = 1
        while d == 1:
            x = (x * x + c) % n; y = (y * y + c) % n; y = (y * y + c) % n; d = math.gcd(abs(x - y), n)
        if d != n: return d
def factor(n, out=None):
    out = {} if out is None else out
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        while n % p == 0: out[p] = out.get(p, 0) + 1; n //= p
    st = [n] if n > 1 else []
    while st:
        m = st.pop()
        if m == 1: continue
        if is_prime(m): out[m] = out.get(m, 0) + 1; continue
        d = rho(m); st += [d, m // d]
    return out
def rep_x2_ky2(m, k):  # k in (1, 2): class-number-one criterion
    if m < 0: return False
    if m == 0: return True
    for p, e in factor(m).items():
        bad = (p % 4 == 3) if k == 1 else (p % 8 in (5, 7))
        if bad and e % 2: return False
    return True
