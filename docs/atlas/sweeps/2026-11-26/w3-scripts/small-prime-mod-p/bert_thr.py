import math
def B(x,N):  # Lean bach_primitive_of_GRH
    return (math.sqrt(x)+2+3/x)*(2/3)*(math.log(N)+5/3)+math.log(x)+1.6
def E0(x): return math.sqrt(x)/20+3
def margin(n,t,Nfac=4,PPc=1.43):
    y=n+t*n  # apex
    A1=1/(y-n); A3=1/(2*n-y); A2=-(A1+A3)
    xs=[n,y,2*n]; As=[A1,A2,A3]
    N=Nfac*n
    Ech=sum(abs(a)*x*B(x,N) for a,x in zip(As,xs))
    Ep=sum(abs(a)*x*E0(x) for a,x in zip(As,xs))
    PP=PPc*math.sqrt(2*n)
    return n/4-Ep/2-Ech/2-PP
def thr(t,Nfac=4):
    lo,hi=10,10**12
    # find smallest n0 with margin>0 for all n>=n0 (margin increasing)
    while hi-lo>1:
        mid=(lo+hi)//2
        if margin(mid,t,Nfac)>0: hi=mid
        else: lo=mid
    return hi
for t in [0.3,0.4,0.5,0.6,0.7,0.8]:
    print(t, thr(t), thr(t,8))
