import math
def B(x,N): return (math.sqrt(x)+2+3/x)*(2/3)*(math.log(N)+5/3)+math.log(x)+1.6
def E0(x): return math.sqrt(x)/20+3
def margin(n,t,Nfac,pp):
    y=n+math.floor(t*n)
    A1=1/(y-n); A3=1/(2*n-y); A2=-(A1+A3)
    xs=[n,y,2*n]; As=[A1,A2,A3]; N=Nfac*n
    Ech=sum(abs(a)*x*B(x,N) for a,x in zip(As,xs))
    Ep=sum(abs(a)*x*E0(x) for a,x in zip(As,xs))
    PP = 1.43*math.sqrt(2*n) if pp=='fine' else (math.sqrt(2*n)+(2*n)**(1/3)*math.log2(2*n))*math.log(2*n)
    return n/4-Ep/2-Ech/2-PP
for Nfac in (4,8):
  for pp in ('fine','crude'):
    best=None
    for t in [i/100 for i in range(20,61,2)]:
        # find last n in [10, 1e7] with margin<=0 (scan geometric then linear)
        lo=10; last=None
        n=10
        while n<10**7:
            if margin(n,t,Nfac,pp)<=0: last=n
            n=int(n*1.01)+1
        if best is None or last<best[1]: best=(t,last)
    print('Nfac',Nfac,pp,'best apex t, last failing n ~',best)
# confirm monotone above threshold for chosen t
t=0.4
fails=[n for n in range(50000,400000) if margin(n,t,8,'crude')<=0]
print('crude Nfac8 t=.4 max fail',max(fails) if fails else None)
fails=[n for n in range(20000,200000) if margin(n,t,4,'fine')<=0]
print('fine Nfac4 t=.4 max fail',max(fails) if fails else None)
