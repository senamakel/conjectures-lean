def spf_sieve(N):
    s=list(range(N+1))
    i=2
    while i*i<=N:
        if s[i]==i:
            for j in range(i*i,N+1,i):
                if s[j]==j: s[j]=i
        i+=1
    return s
def factor(n,s):
    d={}
    while n>1:
        p=s[n]; d[p]=d.get(p,0)+1; n//=p
    return d
