import sys; sys.path.insert(0,'.')
from kappa import kappa, conj34
from fractions import Fraction as Fr
bad=[]; n=0
for k in range(9,1501):
    if k in (9,10,14,16,18,23,25,32): continue
    kp,_=kappa((1,8,k)); c=conj34(k); n+=1
    if kp==c: continue
    r=k%9
    if r==3 and k>=57 and kp==Fr(4*k-3,9*k+9): continue
    if r==5 and k>=50 and kp==Fr(4*k-2,9*k+9): continue
    bad.append((k,r,kp,c))
print("checked",n,"k in [9,1500]; deviations not matching the two corrected branches:",bad)
