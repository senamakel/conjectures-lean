"""Independent exact check for OEIS A301534 (Z.-W. Sun, 2018):
   every prime p > 7 with p = 7 (mod 12) is x^2 + 3*y^2 + 15*2^z with x, y, z >= 0.
For each given p: confirm p is prime (deterministic Miller-Rabin, bases valid below 3.3e24, plus
trial division), p = 7 mod 12, then enumerate EVERY z with 15*2^z <= p and EVERY y with
3y^2 <= p - 15*2^z, testing whether the rest is a perfect square (math.isqrt). Prints the
number of representations (x, y, z). Uses only the standard library; shares no code with hs3.c.
usage: python3 -I verify534.py p [p ...]   (or --neighbours p k: also the k primes = 7 mod 12 on each side)
"""
import sys, math

def is_prime(n):
    if n < 2: return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    for q in small:
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in small:
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def reps(p):
    out = []
    z = 0
    while 15 * 2 ** z <= p:
        m = p - 15 * 2 ** z
        y = 0
        while 3 * y * y <= m:
            r = m - 3 * y * y
            x = math.isqrt(r)
            if x * x == r: out.append((x, y, z))
            y += 1
        z += 1
    return out, z  # z = number of admissible z values

def report(p):
    pr = is_prime(p)
    rs, nz = reps(p)
    zs = sorted({t[2] for t in rs})
    print('p=%d prime=%s p%%12=%d  admissible z: 0..%d  representations=%d  z used=%s%s'
          % (p, pr, p % 12, nz - 1, len(rs), zs[:12], '' if len(zs) <= 12 else '...'))
    return len(rs)

if __name__ == '__main__':
    a = sys.argv[1:]
    if a and a[0] == '--neighbours':
        p, k = int(a[1]), int(a[2])
        report(p)
        for sgn in (-1, 1):
            q, c = p, 0
            while c < k:
                q += 12 * sgn
                if is_prime(q): report(q); c += 1
    else:
        for x in a: report(int(x))
