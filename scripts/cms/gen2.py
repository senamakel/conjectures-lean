import sys, json, math
sys.path.insert(0, sys.argv[0].rsplit('/',1)[0])
from exact import *
import numpy as np
design=json.load(open(sys.argv[1])); cellsf=json.load(open(sys.argv[2])); out=sys.argv[3]
GD=2**40
Phi=np.array(design['Phi']); Phi[np.abs(Phi)<1e-12]=0
K=design['K']
phi=[int(round(x*2**20)) for x in Phi]
assert phi[K]==0
L=K; J=2*L
def tcoef(n):
    T=[[1],[0,1]]
    for m in range(2,n+1):
        a=[0]+[2*x for x in T[m-1]]
        b=T[m-2]+[0]*(len(a)-len(T[m-2]))
        T.append([x-y for x,y in zip(a,b)])
    return T
T=tcoef(L)
qs=[0]*(L+1)
for j in range(J+1):
    k=abs(j-L)
    for i,t in enumerate(T[k]): qs[i]+=phi[k]*t
C=consts(phi,L)
pts=[c[0] for c in cellsf]+[cellsf[-1][1]]
Ns=sorted(set(int(round(x*D0)) for x in pts))
# make sure the first nonzero endpoint is not too small and the region split at theta=1 is a node
if D0 not in Ns: Ns=sorted(set(Ns+[D0]))
ents=[]
for N in Ns:
    th=N/D0; k=int(round(th/(2*math.pi)))
    cl,cu=endvals(N,k)
    ents.append(dict(N=N,k=k,cl=cl,cu=cu,j=0,fl=0,tg=0,Gn=0,en=0,r=0))
for i in range(len(ents)-1):
    e,e2=ents[i],ents[i+1]
    a,b=e['N']/D0,e2['N']/D0
    j=int(math.floor(a/math.pi))
    if b > (j+1)*math.pi - 1e-12:
        e['j']=j+1; e['fl']=1
    else:
        e['j']=j; e['fl']=0
    e['tg']=0 if e2['N']**2<=15*D0**2 else 1
    assert posOK(e,e2), (i,a,b,e)
    e['Gn']=needGn(qs,GD,e,e2)
    assert boundOK(qs,GD,e,e2)
    e['en']=needEn(C,e,e2)
    e['r']=needR(e2)
json.dump(dict(phi=phi,qs=qs,L=L,GD=GD,ents=ents,C=C),open(out,'w'))
n=len(ents)-1
A1=sum(ents[i]['Gn']*(ents[i+1]['N']-ents[i]['N']) for i in range(n))/(GD*D0)/2**20
print('entries',len(ents),'A1cert(normalized)',A1,'C',C,'Theta',ents[-1]['N']/D0)
