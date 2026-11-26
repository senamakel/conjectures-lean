import sys, math
N=int(sys.argv[1])
M=2*N+10
s=bytearray([1])*(M+1); s[0]=s[1]=0
for i in range(2,int(M**0.5)+1):
    if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
primes=[i for i in range(3,M+1) if s[i]]
import bisect
def leg(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
fails={'n+1':[], 'n-1':[], '2n+1':[], '-n-1':[]}
worst={k:(0,0) for k in fails}  # max index count needed
for n in range(1,N+1):
    i=bisect.bisect_right(primes,n)
    issq = math.isqrt(n)**2==n
    issq2 = math.isqrt(2*n)**2==2*n
    need={'n+1':True,'n-1':not issq,'2n+1':True,'-n-1':True}
    cnt=0
    j=i
    while any(need.values()) and j<len(primes) and primes[j]<2*n:
        p=primes[j]; cnt+=1
        if need['n+1'] and leg(n,p)==1: need['n+1']=False; 
        if need['n-1'] and leg(n,p)==-1: need['n-1']=False; worst['n-1']=max(worst['n-1'],(cnt,n))
        if need['2n+1'] and leg(2*n,p)==1: need['2n+1']=False
        if need['-n-1'] and leg(-n,p)==-1: need['-n-1']=False; worst['-n-1']=max(worst['-n-1'],(cnt,n))
        j+=1
    for k,v in need.items():
        if v: fails[k].append(n)
for k,v in fails.items(): print(k, 'failures:', v[:30], len(v))
print('worst prime index needed', worst)
