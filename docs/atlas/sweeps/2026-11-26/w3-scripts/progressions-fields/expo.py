from math import log, sqrt
def ok(x, D, om):
    B = (sqrt(x)+2+3/x)*(2/3)*(log(D)+5/3) + log(x) + 1.6
    lhs = x/2 - sqrt(x)/20 - 3 - B
    rhs = 2*log(x) + 2*1.4*sqrt(x) + om*log(x) + 2*log(2)
    return lhs > rhs
for E in [3,5,6,7]:
    lo, hi = 10.0, 1e60
    while hi/lo > 1.0001:
        m = (lo*hi)**0.5
        om = log(m)/log(log(m))*1.4  # generous omega bound
        if ok((m/4)**(1/E), m, om): hi = m
        else: lo = m
    print("exponent", E, "GRH split-prime argument closes for |D| >= %.3g" % hi)
