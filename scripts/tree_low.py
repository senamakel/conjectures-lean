# Size MTT Algorithm 1 (alg.py) with a lower analytic threshold LOW instead of 2.5e15.
# Usage: python3 tree_low.py LOW [LIM]. Prints the number of enumerated k (candidates). Sizing only.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import alg
from crit import primes_upto
alg.PR = primes_upto(200000)
alg.LOW = int(float(sys.argv[1]))
alg.LIM = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10**6
sys.setrecursionlimit(100000)
tot = nodes = 0
for n in range(1, 16):
    for k in alg.stats: alg.stats[k] = 0
    alg.node(n, [2], [])
    tot += alg.stats['cand']; nodes += alg.stats['nodes']
    if alg.stats['cand']: print(n, alg.stats, flush=True)
print('LOW %.1e total cand %.3e nodes %d' % (alg.LOW, tot, nodes))
