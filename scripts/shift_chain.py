# Prime chain for Cramer/Shift/Small.lean: python3 scripts/shift_chain.py > chain107.txt, then
# python3 scripts/shift_chain_lean.py (reads chain107.txt) writes Cramer/Shift/Small.lean.
import math,sys
N=100_300_000
s=bytearray([1])*(N+1); s[0]=s[1]=0
for i in range(2,int(N**.5)+1):
    if s[i]: s[i*i::i]=bytearray(len(range(i*i,N+1,i)))
def k_of(p):
    k=(p**16).bit_length()-1
    assert 2**k<=p**16<2**(k+1)
    return k
def ok(p,q):
    k=k_of(p)
    return (q-p)**2*(16*10**6)**2 <= 11449*p*(6931*k)**2
chain=[2]; p=2
while p < 100_000_000:
    g=int(1.07*math.sqrt(p)*math.log(p))+2
    q=min(p+g,N)
    while not (s[q] and ok(p,q)): q-=1
    assert q>p,p
    chain.append(q); p=q
print(len(chain), chain[-1], file=sys.stderr)
print(repr([(q,k_of(q)) for q in chain]))
# brute check of PrimeInShortInterval(1.07) at small x: worst ratio
