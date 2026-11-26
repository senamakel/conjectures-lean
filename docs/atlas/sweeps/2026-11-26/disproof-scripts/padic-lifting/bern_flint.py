import flint, sys, time
p=int(sys.argv[1])
def vp(x):
    x=abs(int(x)); v=0
    while x%p==0: x//=p; v+=1
    return v
for k in map(int,sys.argv[2:]):
    t=time.time(); B=flint.fmpq.bernoulli(k)
    q=B/k
    print("k=%d v_%d(B_k/k)=%d  (%.1fs)"%(k,p,vp(q.p)-vp(q.q),time.time()-t))
