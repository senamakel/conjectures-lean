from yscan import fams
from ytest import *
rows=[]
for name,L in fams:
    if L[0]<4: continue
    z=coeffs('Z',L); m=lcmin(z)
    rows.append((float(m),name,L[0]))
rows.sort()
for r in rows[:10]: print(r)
