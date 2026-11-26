from ytest import *
import itertools
def report(name,L):
    n=L[0]
    y=coeffs('Y',L); c=[y[0]]+[y[j]-y[j-1] for j in range(1,n//2+1)]
    m=lcmin(y)
    neg=any(x<0 for x in c)
    # LC slack at each interior index relative
    sl=[ (y[i]**2-y[i-1]*y[i+1])/ (y[i]**2) for i in range(1,n)]
    print(f"{name:40s} r={n} c={['%.3g'%x for x in c]} minLCslack={min(sl):.3e} c2/c1={c[2]/c[1] if n>=4 else 0:.3f}{' NEG' if neg else ''}{' NONLC' if m is not None and m<1 else ''}")
fams=[]
for s in [3,10,100]:
  for m in [2,3,4]:
    for b in [0,1,2]:
      L=line(s)
      for _ in range(m-1): L=prod(L,line(s))
      for _ in range(b): L=prod(L,boolean(1))
      for r in range(4,min(L[0],8)+1):
        fams.append((f'trunc{r}(U2,{s}^{m} x B{b})',truncate(L,r)))
for q in [2,3,7]:
  for d in [2,3,4]:
    for t in [0,1,2,3,10]:
      L=Dlat(d,t,q)
      for r in range(4,min(L[0],8)+1):
        fams.append((f'trunc{r}(PG{d}_{q} x B{t})',truncate(L,r)))
  for d in [5,6,7]:
    fams.append((f'PG{d}_{q} minus pt',pg_minus_point(d,q)))
for name,L in fams:
    if L[0]>=4: report(name,L)
