import re, sys
sys.path.insert(0, sys.argv[2])
from conjf import conj
from fractions import Fraction as F
t = open(sys.argv[1]).read()
pts = []
for m in re.finditer(r'<path fill="none" stroke-width="2"[^>]*stroke="rgb\(0%, 0%, 0%\)"[^>]*d="([^"]*)"', t):
    pts += [(float(a), float(b)) for a, b in re.findall(r'([-\d.]+) ([-\d.]+)', m.group(1))]
x0, y0 = 82.999998, 58.456161   # k=9, 3/10 (table value)
y1 = 380.48116                   # 4/9 horizontal line
bx = 50.754164/9; by = (y1-y0)/(4/9-0.3)
seen = {}
for x, y in pts:
    k = round(9 + (x-x0)/bx); v = 0.3 + (y-y0)/by
    seen[k] = v
for k in sorted(seen):
    v = seen[k]; best = min((F(a,b) for b in range(1,600) for a in [round(v*b)] if a>0), key=lambda f: (abs(float(f)-v), f.denominator))
    print(k, k%9, f"{v:.7f}", "nearest", best, f"{float(best):.7f}", "conj", conj(k) if k>8 else '-', f"{float(conj(k)):.7f}" if k>8 else '')
