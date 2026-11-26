"""Box lower bounds mirroring the Lean definitions (exact Fractions)."""
from fractions import Fraction as F
import math

LPIlo, LPIhi = F(1144, 1000), F(11448, 10000)
glo, ghi = F(57688, 100000), F(5774, 10000)
l2lo, l2hi = F(6931471803, 10**10), F(6931471808, 10**10)
l3lo = F(1622, 1024) * l2lo
l5lo = F(2377, 1024) * l2lo
pihi = F(31416, 10000)
h2lo, h2hi = l2lo / 2, l2hi / 2
h3lo = l3lo / 2
c2lo, c2hi = 3 + 6 * l2lo, 3 + 6 * l2hi
c1lo = -3 + LPIlo / 2 + glo / 2 + l2lo / 2


def mulLo(a, b, q): return min(a * q, b * q)


def common(Xa, sa, sb, la, lb):
    d = dict()
    d['mEsh'] = (1 - F(1, Xa)) * (LPIlo + glo) - 2 * (lb + 2) / Xa
    d['dlo'] = (3 + la / 2) * sb ** 2 / (sb - 1) ** 2 - sa / (sa - 1) ** 2
    d['dhi'] = (3 + lb / 2) * sa ** 2 / (sa - 1) ** 2
    d['epshi'] = 3 + 4 / (sa - 1) + lb * sa / (sa - 1)
    return d


def pc0(Xa, sa, big):
    return -1 - ghi - F(1, 4) / sa - F(12, Xa) if big else F(-2)


def F1Lo(Xa, sa, sb, la, lb, big):
    c = common(Xa, sa, sb, la, lb)
    p = pc0(Xa, sa, big)
    Q = c['mEsh'] + 2 * p + F(605, 100) - F(1, Xa) - l2hi * (1 + F(1, Xa)) - 3 - 4 / (sa - 1) - lb / (sa - 1)
    W = la + c['mEsh'] + 2 * p + F(62, 10) - F(1, Xa) - l2hi * (1 + F(1, Xa))
    V = c1lo * lb - F(7, 2) - pihi ** 2 / 6 - (4 + lb) / (2 * (sa - 1)) - (lb - h2lo) ** 2 / 2 - (lb - h3lo) ** 2 / 2
    return mulLo(sa, sb, Q) + mulLo(c['dlo'], c['dhi'], W) + V, (Q, W, V)


def F2aLo(Xa, sa, sb, la, lb):
    c = common(Xa, sa, sb, la, lb)
    etalo, etahi = h2lo / lb, h2hi / la
    A = sa ** 2 * etalo * (2 - etahi) - (1 + F(1, 4 * Xa))
    Klo, Khi = sa + c['dlo'], sb + c['dhi']
    kaphi = sb + c['epshi']
    mulo = sa * (1 - etahi) ** 2
    mEsh2 = c['mEsh'] / 2
    RChi = (lb - h2lo) ** 2 / 2 + l2hi * (Khi * (1 + F(1, Xa)) - la / 2) + (lb - h3lo) ** 2 / 2
    v = (A - F(15, 100) * sb - 3 * lb - 3 + 2 * Klo * mEsh2 + LPIlo / 2 * la - (pihi ** 2 / 6 - glo * la / 2)
         - RChi + 11 * mulo - 8 * kaphi + 2 * mulo * 3 * l2lo)
    return v, (A, mEsh2)


def F2bLo(Xa, sa, sb, la, lb):
    c = common(Xa, sa, sb, la, lb)
    etalo = h2lo / lb
    lam2lo = -c2hi / (sa - c2hi)
    nus = 1 + F(1, 2 * Xa)
    Q = (-F(15, 100) + c['mEsh'] - l2hi * (1 + F(1, Xa)) + c2lo - l2hi * nus + h2lo * (h2lo / lb)
         + 2 * nus * (1 - etalo) ** 2 * (lam2lo - 3 * l2hi) - 3 - 4 / (sa - 1) - lb / (sa - 1))
    W = c['mEsh'] - l2hi * (1 + F(1, Xa))
    V = (c1lo * lb - F(7, 2) - pihi ** 2 / 6 - (4 + lb) / (2 * (sa - 1)) + c2lo * (3 + la)
         - (lb - h2lo) ** 2 / 2 - (lb - h3lo) ** 2 / 2)
    return mulLo(sa, sb, Q) + mulLo(c['dlo'], c['dhi'], W) + V, (Q, W, V)


def R5Lo(Xa, sa, sb, la, lb):
    # log5 (K/2 - K/x + l/2) - (l - log5/2)^2/2 with K >= sa + 1 + la/2, K/2 - K/x = K(1/2 - 1/x)
    Klo = sa + 1 + la / 2
    return l5lo * (Klo * (F(1, 2) - F(1, Xa)) + la / 2) - (lb - l5lo / 2) ** 2 / 2, None


def kbounds(X, m=64):
    """2^k <= X^m <= 2^(k+1): log X in [k/m log2lo, (k+1)/m log2hi]"""
    k = (X ** m).bit_length() - 1
    return k, k + 1


def sqrt_lo(X, den=1000):
    a = math.isqrt(X * den * den)
    while F(a, den) ** 2 > X: a -= 1
    return F(a, den)


def sqrt_hi(X, den=1000):
    a = math.isqrt(X * den * den) + 1
    while F(a, den) ** 2 < X: a += 1
    return F(a, den)


def box(Xa, Xb, m=64):
    ka, _ = kbounds(Xa, m)
    _, kb = kbounds(Xb, m)
    la = F(ka, m) * l2lo
    lb = F(kb, m) * l2hi
    sa, sb = sqrt_lo(Xa), sqrt_hi(Xb)
    return dict(Xa=Xa, Xb=Xb, ka=ka, kb=kb, la=la, lb=lb, sa=sa, sb=sb)
