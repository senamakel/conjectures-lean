from invs import *
from flags import all_subsets
def beta_weights(f, n):
    """coefficient polynomial of beta(T) in f evaluated on rank-n posets: sum_{S >= T} w(comp(S))."""
    comp_of={}
    for c in compositions(n):
        S=[];acc=0
        for x in c[:-1]:
            acc+=x;S.append(acc)
        comp_of[tuple(S)]=c
    W={}
    for T in all_subsets(n-1):
        s=ZERO
        for S in all_subsets(n-1):
            if set(T)<=set(S):
                w=f.get(comp_of[S])
                if w is not None: s+=w
        W[T]=s
    return W
if __name__=="__main__":
    import sys
    I=build(9)
    name=sys.argv[1]; n=int(sys.argv[2])
    W=beta_weights(I[name],n)
    for T in sorted(W,key=lambda s:(-len(s),s)):
        print(T, W[T])
