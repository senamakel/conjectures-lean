import sys,random,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from hh import run
from flint import fmpq
random.seed(int(sys.argv[1])); K=int(sys.argv[2]); T=float(sys.argv[3])
vals=[fmpq(0),fmpq(1,100),fmpq(1,10),fmpq(1,2),fmpq(1),fmpq(2),fmpq(10),fmpq(100)]
t0=time.time(); n=0
while time.time()-t0<T:
    d=random.randint(2,9)
    pc=[fmpq(0)]+[random.choice(vals) for _ in range(d)]
    pc[2]=pc[1]; 
    if pc[d]==0: pc[d]=fmpq(1)
    o,p=run(pc,K); n+=1
    bad=[(k,neg) for k,deg,neg in o if neg]
    if bad or isinstance(p,tuple):
        print("HIT",[str(c) for c in pc],bad[:2],p if isinstance(p,tuple) else '',flush=True)
print("done",n,"polys",flush=True)
