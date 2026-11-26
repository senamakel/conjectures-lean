from math import log, sqrt
def ok(x, p, psic=1.4):
    B = (sqrt(x)+2+3/x)*(2/3)*(log(p)+5/3) + log(x) + 1.6
    lhs = x/2 - sqrt(x)/20 - 3 - B
    rhs = 2*log(x) + 2*psic*sqrt(x)
    return lhs > rhs
# least x (as function of p) that works
def xmin(p):
    lo, hi = 2, 10**12
    while lo < hi:
        m = (lo+hi)//2
        # monotone in x for large x
        if ok(m, p): hi = m
        else: lo = m+1
    return lo
for e in [3,4,5,6,7,8,10,12,15,20,30,50,100]:
    p = 10**e
    xm = xmin(p)
    print(e, xm, round(xm/log(p)**2,3))
# threshold for x = sqrt p
def thr(f):
    lo, hi = 10, 10**40
    while hi/lo > 1.001:
        m = (lo*hi)**0.5
        if ok(int(f(m)), m): hi = m
        else: lo = m
    return hi
print("sqrt p:", "%.3g" % thr(lambda p: sqrt(p)))
for c in [1/3, 0.3, 0.27, 0.25, 0.2]:
    print("p^%.3f:"%c, "%.3g" % thr(lambda p, c=c: p**c))
