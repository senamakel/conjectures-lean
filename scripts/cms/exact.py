# Exact integer mirror of Cramer/CMS/Cells.lean definitions.
from math import comb, factorial
D0 = 1048576
SS = 18446744073709551616
PIL = 314159265358979323846
PIH = 314159265358979323847
TE = 10**20
def cosNum(n, p, q):
    return sum((-1)**i * p**(2*i) * q**(2*(n-1)-2*i) * (factorial(2*(n-1))//factorial(2*i)) for i in range(n))
def cosDen(n, q): return q**(2*(n-1)) * factorial(2*(n-1))
def tNum(N, k): return N*TE - 2*k*PIH*D0
def fdiv(a,b): return a//b   # floor for b>0
def cdiv(a,b): return -((-a)//b)
def endvals(N, k):
    p = tNum(N,k); q = D0*TE
    n14, d14 = cosNum(14,p,q), cosDen(14,q)
    n13, d13 = cosNum(13,p,q), cosDen(13,q)
    # cl*d14*TE <= (n14*TE - 2k d14)*SS  -> cl = floor(((n14*TE-2k d14)*SS)/(d14*TE))
    cl = fdiv((n14*TE - 2*k*d14)*SS, d14*TE)
    cu = cdiv((n13*TE + 2*k*d13)*SS, d13*TE)
    return cl, cu
def endOK(N,k,cl,cu):
    p = tNum(N,k); q = D0*TE
    n14, d14 = cosNum(14,p,q), cosDen(14,q)
    n13, d13 = cosNum(13,p,q), cosDen(13,q)
    return cl*d14*TE <= (n14*TE - 2*k*d14)*SS and (n13*TE + 2*k*d13)*SS <= cu*d13*TE
def Qp(qs, A, T, i):
    n=len(qs)
    return sum(qs[j]*comb(j,i)*A**(j-i)*T**(n-1-j) for j in range(n) if i<=j)
def Ub(qs, A, T, R):
    return sum(abs(Qp(qs,A,T,i))*R**i for i in range(len(qs)))
def cLo(e,e2):
    if e['fl']==0: return min(e['cl'],e2['cl'])
    return min(e['cl'],e2['cl']) if e['j']%2==0 else -SS
def cHi(e,e2):
    if e['fl']==0: return max(e['cu'],e2['cu'])
    return SS if e['j']%2==0 else max(e['cu'],e2['cu'])
def posOK(e,e2):
    ok = e['N']<=e2['N'] and e2['N']*TE <= (e['j']+1)*PIL*D0
    if e['fl']==0: return ok and e['j']*PIH*D0 <= e['N']*TE
    return ok and e['j']>=1 and (e['j']-1)*PIH*D0 <= e['N']*TE
def needGn(qs, GD, e, e2):
    lo, hi = cLo(e,e2), cHi(e,e2)
    U = Ub(qs, lo+hi, 2*SS, hi-lo)
    K = len(qs)-1
    T = 2*SS
    N = e['N']
    if e['tg']==0:
        num = (360*D0**4 + N**4 - 30*N**2*D0**2)*U*GD
        den = 360*D0**4*T**K
    else:
        num = (2*SS-2*lo)*U*GD*D0**2
        den = N**2*SS*T**K
    return cdiv(num, den)
def boundOK(qs,GD,e,e2):
    lo, hi = cLo(e,e2), cHi(e,e2)
    if lo>hi: return False
    U = Ub(qs, lo+hi, 2*SS, hi-lo); K=len(qs)-1; T=2*SS; N=e['N']
    if e['tg']==0:
        return e2['N']**2 <= 15*D0**2 and (360*D0**4 + N**4 - 30*N**2*D0**2)*U*GD <= e['Gn']*360*D0**4*T**K and 30*N**2*D0**2 <= 360*D0**4+N**4
    return N>0 and (2*SS-2*lo)*U*GD*D0**2 <= e['Gn']*N**2*SS*T**K
def aco(c, j):
    return c(j+1) - 2*c(j) + (0 if j==0 else c(j-1))
def consts(phi, L):
    J=2*L
    def c(j): 
        k=abs(j-L)
        return phi[k] if (j<=J and k<len(phi)) else 0
    C1a=sum(abs(c(j))*(abs(j-L)+1) for j in range(J+1))
    C1b=sum(abs(c(j))*(abs(j-L)+1)**2 for j in range(J+1))
    C2a=sum(abs(aco(c,j))*abs(j-L) for j in range(J+1))
    C2b=sum(abs(aco(c,j))*abs(j-L)**2 for j in range(J+1))
    As=sum(abs(aco(c,j)) for j in range(J+1))
    return C1a,C1b,C2a,C2b,As
def needEn(C, e, e2):
    C1a,C1b,C2a,C2b,As=C
    if e2['N']<=D0: return C1a*D0+2*e2['N']*C1b
    return cdiv((2*C2a*D0**2+2*e['N']*C2b*D0)*D0, e['N']**2)
def needR(e2):
    N=e2['N']
    r=-200
    while True:
        if r>=0:
            if N**4 <= D0**4*2**r: return r
        else:
            if N**4*2**(-r) <= D0**4: return r
        r+=1
