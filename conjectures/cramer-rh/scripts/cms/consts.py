import json, sys, math
sys.path.insert(0,'gen')
from exact import *
from fractions import Fraction as Fr
d=json.load(open(sys.argv[1]))
ents=d['ents']; GD=d['GD']; phi=d['phi']; L=d['L']; J=2*L
C1a,C1b,C2a,C2b,As=d['C']
n=len(ents)-1
A1G=sum(ents[i]['Gn']*(ents[i+1]['N']-ents[i]['N']) for i in range(n))          # /(GD*D0)
A1e=sum(ents[i]['en']*(ents[i+1]['N']-ents[i]['N']) for i in range(n))          # /(D0*D0)
A2Gp=sum(ents[i]['Gn']*(ents[i+1]['N']-ents[i]['N'])*ents[i]['r'] for i in range(n) if ents[i]['r']>0)   # /(4 GD D0)
A2Gn=sum(ents[i]['Gn']*(ents[i+1]['N']-ents[i]['N'])*(-ents[i]['r']) for i in range(n) if ents[i]['r']<0)
A2ep=sum(ents[i]['en']*(ents[i+1]['N']-ents[i]['N'])*ents[i]['r'] for i in range(n) if ents[i]['r']>0)
A2en=sum(ents[i]['en']*(ents[i+1]['N']-ents[i]['N'])*(-ents[i]['r']) for i in range(n) if ents[i]['r']<0)
TVG=ents[0]['Gn']+ents[n-1]['Gn']+sum(abs(ents[i+1]['Gn']-ents[i]['Gn']) for i in range(n-1))
TVe=ents[0]['en']+ents[n-1]['en']+sum(abs(ents[i+1]['en']-ents[i]['en']) for i in range(n-1))
Theta=ents[-1]['N']/D0
S=phi[0]+2*sum(phi[1:])
sc=2**20
l2=math.log(2)
out=dict(A1G=A1G/(GD*D0)/sc, A1e=A1e/(D0*D0)/sc, A2G=(A2Gp-A2Gn)/(4*GD*D0)*l2/sc, A2e=(A2ep-A2en)/(4*D0*D0)*l2/sc,
  TVG=TVG/GD/sc, TVe=TVe/D0/sc, Theta=Theta, S=S/sc, As=As/sc, C1a=C1a/sc, C1b=C1b/sc)
print(out)
json.dump(dict(raw=dict(A1G=A1G,A1e=A1e,A2Gp=A2Gp,A2Gn=A2Gn,A2ep=A2ep,A2en=A2en,TVG=TVG,TVe=TVe,S=S,As=As),norm=out),open(sys.argv[2],'w'))
