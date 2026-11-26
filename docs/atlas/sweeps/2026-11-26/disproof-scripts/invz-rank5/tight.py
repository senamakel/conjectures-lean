"""List the Whitney numbers of the rank-5 database matroids with c2 == W1 (equality in the proof)."""
import sys, lzma, os
from lattice import rank_table_from_bases, revlex_bases, dual_bases
from dbscan import flats_by_rank, sub
DB = sys.argv[1]
seen = {}
for n in range(6, 10):
    with lzma.open(os.path.join(DB, f'allr{n-5}n{n:02d}.txt.xz'), 'rt') as f:
        for s in f:
            rk = rank_table_from_bases(n, dual_bases(n, revlex_bases(n, n - 5, s.strip())))
            fb = flats_by_rank(n, rk)
            pts, lns, hyp = fb[1], fb[2], fb[4]
            a14 = sum(1 for H in hyp for x in pts if sub(x, H)); a24 = sum(1 for H in hyp for L in lns if sub(L, H))
            if a24 - a14 - len(lns) + len(pts) == len(pts):
                key = tuple(len(fb[i]) for i in range(6)); seen[key] = seen.get(key, 0) + 1
print(seen)
