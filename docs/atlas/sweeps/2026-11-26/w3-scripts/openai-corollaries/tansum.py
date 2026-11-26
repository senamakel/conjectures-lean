import numpy as np, math
N=10**8; B=10**7
S=0.0; A=0.0; A15=0.0; big=[]
out=[]
for s in range(1,N+1,B):
    n=np.arange(s,min(s+B,N+1),dtype=np.float64)
    t=np.tan(n)
    S+=np.sum(t/n**2); A+=np.sum(np.abs(t)/n**2); A15+=np.sum(np.abs(t)/n**1.5)
    r=np.abs(t)/n; i=np.argmax(r); big.append((int(n[i]),float(t[i]),float(r[i])))
    e=s+B-1
    out.append((e,S,A,A15))
for e,S_,A_,A15_ in out:
    if e in (10**7,2*10**7,5*10**7,10**8): print(e,'sum tan/n^2=%.6f'%S_,'sum|tan|/n^2=%.6f'%A_,'sum|tan|/n^1.5=%.4f'%A15_)
for k in (10,100,1000,10**4,10**5,10**6):
    n=np.arange(1,k+1,dtype=np.float64); t=np.tan(n); print(k,'%.6f'%np.sum(t/n**2),'%.6f'%np.sum(np.abs(t)/n**2))
print('max |tan n|/n per 1e7 block', big)
# check mu=2 prediction: max over blocks of log|tan n|/log n
