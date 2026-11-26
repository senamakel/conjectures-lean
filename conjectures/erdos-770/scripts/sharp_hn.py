import math, sys
from math import gcd
from multiprocessing import Pool
def isprime(p):
    if p < 2: return False
    if p % 2 == 0: return p == 2
    i = 3
    while i * i <= p:
        if p % i == 0: return False
        i += 2
    return True
def divisors(n):
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i * i != n: ds.append(n // i)
        i += 1
    return ds
def info(n):
    ds = divisors(n)
    good = [d + 1 for d in ds if isprime(d + 1)]
    P = max(good)
    m = (1 << n) - 1
    g = gcd(m, pow(3, n, m) - 1)
    for p in good:
        while g % p == 0: g //= p
    E = 3
    gg = g
    while gg != 1:
        E += 1
        gg = gcd(gg, pow(E, n, gg) - 1)
    # largest bad prime info: g itself (product of bad primes for M=3)
    return (n, P, E, g.bit_length())
if __name__ == '__main__':
    N = int(sys.argv[1]); procs = int(sys.argv[2])
    with Pool(procs) as pool:
        res = pool.map(info, range(2, N + 1), chunksize=200)
    out = open(f'hn_{N}.txt', 'w')
    for r in res: out.write('%d %d %d %d\n' % r)
    out.close()
    worst = sorted(((E - 1) / math.log(n) ** 2, n, E, P) for (n, P, E, b) in res if E > P)
    print('count E>P', len(worst))
    print('top', worst[::-1][:15])
    ws = [w for w in worst if w[1] >= 5]
    print('top n>=5', ws[::-1][:10])
    print('max E', max(r[2] for r in res))
