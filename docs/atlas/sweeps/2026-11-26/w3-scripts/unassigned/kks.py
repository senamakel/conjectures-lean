import sys, math
N=int(sys.argv[1])
s=bytearray([1])*(N+1); s[0]=s[1]=0
for i in range(2,int(N**0.5)+1):
    if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
pr=[i for i in range(3,N+1) if s[i]]
exc=[]; worst=(0,0)
for p in pr:
    for q in pr:
        if q==p: continue
        if pow(q,(p-1)//2,p)==1: break
    if q*q>=p: exc.append((p,q))
    worst=max(worst,(q/math.sqrt(p) if p>1000 else 0,p))
print('exceptions (p, least odd prime QR) with q>=sqrt p:',exc)
print('max q/sqrt(p) for p>1000:',worst)
