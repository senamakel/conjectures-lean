import sys, random, numpy as np
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from perc import g6, configs
tol=1e-12
def run(n,E,ps,tag,out):
    w,C=configs(n,E,ps)
    conn=lambda a,b: ((C[:,a]>>b)&1)==1
    for o in range(n):
        EH=[e for e in E if o not in e]; psH=[p for e,p in zip(E,ps) if o not in e]
        wH,CH=configs(n,EH,psH)
        C0=C[:,o]
        for A in range(1,1<<n):
            if (A>>o)&1 or bin(A).count('1')<3: continue
            hit=(C0&A)!=0; wA=w*hit; wN=w*(~hit)
            al=[a for a in range(n) if A>>a&1]
            for b in range(n):
                if b==o or (A>>b)&1: continue
                lhs=(wA*conn(o,b)).sum()
                pre=[(wA*conn(a,b)).sum() for a in al]
                q2=[(wN*conn(a,b)).sum() for a in al]
                q3=[(wH*(((CH[:,a]>>b)&1)==1)).sum() for a in al]
                for name,key in (('Q2',q2),('Q3',q3)):
                    m=min(key); ties=[j for j in range(len(al)) if key[j]<=m+tol]
                    if all(lhs<pre[j]-tol for j in ties):
                        out.append((name,tag,o,b,A,lhs-max(pre[j] for j in ties)))
lines=open(sys.argv[1]).read().split(); mode=sys.argv[2]; random.seed(int(sys.argv[3]))
lo,hi=map(int,sys.argv[4].split(':')) if len(sys.argv)>4 else (0,len(lines))
out=[]
for li in range(lo,min(hi,len(lines))):
    n,E=g6(lines[li])
    plist=[[0.5]*len(E)] if mode=='half' else [[random.choice([0.05,0.2,0.5,0.8,0.95,1.0]) for _ in E] for _ in range(int(mode))]
    for ps in plist: run(n,E,ps,lines[li],out)
seen=set()
for r in out:
    if (r[0],r[1]) in seen: continue
    seen.add((r[0],r[1])); print(r,flush=True)
print("done",len(out))
