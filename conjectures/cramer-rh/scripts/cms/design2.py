import numpy as np, json, sys
from design import leftout_solve
M=int(sys.argv[1]); jsub=int(sys.argv[2]); Ks=[int(k) for k in sys.argv[3].split(',')]
best=None
for K in Ks:
    J,Phi=leftout_solve(M,K,4.0,nt=8000,jsub=jsub)
    print(M,K,jsub,J,flush=True)
    if best is None or J>best[0]: best=(J,K,Phi)
J,K,Phi=best; Phi=Phi/Phi[0]
json.dump(dict(M=M,K=K,Phi=Phi.tolist(),J=J),open(f'design_M{M}_j{jsub}.json','w'))
