import sys, math
from gen import *
def plan2(c,Qstart,Qend):
    ivs=[];Q=Qstart
    while Q<Qend:
        best=None
        for r in [2.0,1.6,1.4,1.3,1.2,1.15,1.1,1.07,1.05,1.03,1.02,1.01,1.005]:
            Qb=min(Qend,2**int(math.ceil(Q.bit_length()*r)) if Q.bit_length()*r>Q.bit_length()+1 else int(Q*(2**(r*Q.bit_length()-Q.bit_length()))))
            if Qb<=Q: continue
            d=data(Q,Qb,c)
            if d['v']>0 and d['side']: best=d;break
        if best is None:
            for m in [F(3,2),F(5,4),F(9,8),F(17,16)]:
                Qb=int(Q*m); d=data(Q,Qb,c)
                if d['v']>0 and d['side']: best=d;break
        if best is None: raise SystemExit("FAIL %d"%Q.bit_length())
        ivs.append(best); Q=best['Qb']
    return ivs
def q(fr): return "(%d / %d : ℝ)"%(fr.numerator,fr.denominator) if fr.denominator!=1 else "(%d : ℝ)"%fr.numerator
def lemma(name,d,cstr):
    return f"""theorem {name} (q : ℕ) (h1 : {d['Qa']} ≤ q) (h2 : q < {d['Qb']}) : GoodQ {cstr} q :=
  goodQ_of_data q {d['Qa']} {d['Qb']} {d['ka']} {d['kb']} {d['x']} {q(d['s1'])} {q(d['s2'])} {d['k1']} {d['k2']} h1 h2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [SideOK, iEs, iβ₂, ik₁, iK₁, iK₂, lpLo, lpHi, smallP])
    (by norm_num [PhiLo, iK₁, iK₂, ik₁, ik₂, iEs, iβ₁, iβ₂, iW, iA, lpLo, lpHi, smallP, max_def])
"""
if __name__=="__main__":
    c=F(sys.argv[1]); lo=int(sys.argv[2]); hi=int(sys.argv[3]); cstr=sys.argv[4]
    ivs=plan2(c,2**lo,2**hi)
    out=[]
    for i,d in enumerate(ivs): out.append(lemma(f"good_{i}",d,cstr))
    print("\n".join(out))
    print("-- intervals:",len(ivs), file=sys.stderr)
    print(" ".join(str(d['Qb']) for d in ivs), file=sys.stderr)
