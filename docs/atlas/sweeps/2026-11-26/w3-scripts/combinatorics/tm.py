# Transfer-matrix proof of an empirical linear recurrence for a(n) = # (n+1) x w arrays over 0..q-1, row-pair constraint ok(r,s)
import itertools, sys
def prove(w,q,ok,coeffs,data,offset=1):
    rows=list(itertools.product(range(q),repeat=w)); N=len(rows)
    T=[[1 if ok(r,s) else 0 for s in rows] for r in rows]
    one=[1]*N
    def mul(M,v): return [sum(a*b for a,b in zip(row,v)) for row in M]
    # seq a(n)=1^T T^n 1 for n>=offset; check data
    vecs=[one]; 
    for i in range(N+len(coeffs)+len(data)+2): vecs.append(mul(T,vecs[-1]))
    seq=[sum(v) for v in vecs]  # seq[n] = 1^T T^n 1
    assert seq[offset:offset+len(data)]==data, (seq[offset:offset+5],data[:5])
    d=len(coeffs)
    # claimed: seq[n]=sum c_i seq[n-i], i=1..d, for n>=offset+d. Rigorous: let u_n = seq[n]-sum c_i seq[n-i]; u_n = 1^T T^(n-d) P(T)1, linear recurrent with char poly of T (deg N),
    # so u_n=0 for all n>=d iff u_n=0 for n=d..d+N-1. (Cayley-Hamilton)
    bad=[n for n in range(d, d+N) if seq[n]-sum(c*seq[n-i-1] for i,c in enumerate(coeffs))!=0]
    return N, bad, min([n for n in range(d,d+N)] ) 
if __name__=='__main__':
    ok=lambda r,s: all(r[j]+r[j+1]+s[j]+s[j+1]>=4 for j in range(len(r)-1))
    coeffs=[15,43,-381,-42,1696,-590,-2216,1085,858,-456,-88,48]
    data=[336,5736,91157,1486258,24057629,390354307,6329171799,102644935902,1664547601646,26993866274311,437754652218346,7099004652318411,115123459690848087,1866939760799593583,30275877954690891176]
    N,bad,_=prove(3,3,ok,coeffs,data)
    print("states",N,"recurrence fails at n (seq index) =",bad)
