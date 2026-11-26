# E_n mod N for odd N via E_n == sum_{a=0}^{N-1} (-1)^a (2a+1)^n (mod N)  [from E_n(x)+E_n(x+N)=2 sum (-1)^a (x+a)^n]
import sys
from sympy import euler, isprime, factorint
def Emod(n,N):
    s=0
    for a in range(N):
        t=pow(2*a+1,n,N)
        s = s+t if a%2==0 else s-t
    return s%N
# sanity: compare with sympy exact Euler numbers
for N in (3,5,7,9,15,21,25,27,35,45):
    for n in range(0,40,2):
        assert Emod(n,N)==euler(n)%N, (n,N)
print('formula ok')
print('E12 =',euler(12), factorint(euler(12)))
m=13*41581
print('41581 prime',isprime(41581),'m',m)
print('E_{m-1} mod m =',Emod(m-1,m))
