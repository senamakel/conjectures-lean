import sys, math
def primes(n):
    s=[1]*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=[0]*len(s[i*i::i])
    return [i for i in range(n+1) if s[i]]
P=primes(5000)
def g(q):
    units=sum(1 for a in range(q) if math.gcd(a,q)==1)
    seen={1%q}; frontier=[1%q]; gens=[]
    for p in P:
        if q%p==0: continue
        gens.append(p%q)
        # recompute closure incrementally
        frontier=list(seen)
        while frontier:
            r=frontier.pop()
            for s in gens:
                t=r*s%q
                if t not in seen: seen.add(t); frontier.append(t)
        if len(seen)==units: return p
for q in range(3,int(sys.argv[1])):
    print(q,g(q))
