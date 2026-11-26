import sys,io
from lattices import *
from invs import *
from fractions import Fraction as Fr
I=build(int(sys.argv[1]))
def co(name,L):
    n,al=L; p=evaluate(I[name],al,n); c=[int(x) for x in p.coeffs()]; return c+[0]*(n+1-len(c))
def lcinfo(c):
    bad=[i for i in range(1,len(c)-1) if c[i]**2<c[i-1]*c[i+1]]
    unim=all(c[i]<=c[i+1] for i in range(len(c)//2)) # palindromic check rough
    return bad
for r in range(3,int(sys.argv[1])+1):
  for q in [2,3,4,5]:
    for k in range(1,r):
      L=bose_burton(r,k,q)
      P=co('P',L);Q=co('Q',L);Y=co('Y',L);Z=co('Z',L)
      out=[]
      for nm,c in [('P',P),('Q',Q),('Y',Y),('Z',Z)]:
          # strip trailing zeros for P,Q
          cc=c[:max(i for i,x in enumerate(c) if x!=0)+1]
          b=lcinfo(cc)
          nonuni=any(cc[i-1]>cc[i]<cc[i+1] for i in range(1,len(cc)-1))
          if b or nonuni: out.append(f'{nm}:LCfail@{b}{" NONUNIMODAL" if nonuni else ""}')
      print(r,q,k,' '.join(out) if out else 'ok', 'Q=',Q[:4] if out else '')
