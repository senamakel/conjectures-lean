# Independent exact check of GMU Conjecture 5.6 failures: b_M(n)=[x^n] prod_{j>=0} (1-x^{2^j})^{-M}, M=2^m-1.
# Method: plain truncated power-series multiplication by 1/(1-x^{2^j}) M times (Python big ints), no recursion/upsampling.
def b_series(M, N):
    p=[1]+[0]*N
    j=1
    while j<=N:
        for _ in range(M):
            for n in range(j,N+1): p[n]+=p[n-j]
        j*=2
    return p
def nu2(x):
    if x==0: return 10**9
    v=0
    while x%2==0: x//=2; v+=1
    return v
for m,k,n in [(1,3,1),(3,5,1),(3,6,1),(3,7,1),(3,9,1),(4,6,1),(4,7,1),(4,9,1),(5,7,1),(5,8,1),(5,9,1),(6,8,1),(6,11,1)]:
    M=2**m-1; A=2**(k+1)*n; B=2**(k-1)*n
    p=b_series(M,A)
    d=p[A]-p[B]; need=4*((k+1)//2)-2
    print(f"m={m} M={M} k={k} n={n}: b({A})={p[A]}, b({B})={p[B]}, diff={d}, nu2={nu2(d)}, required 2^{need}: {'HOLDS' if d % 2**need==0 else 'FAILS'}")
