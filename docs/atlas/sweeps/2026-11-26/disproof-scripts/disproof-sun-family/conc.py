import sys, math
# conc.py Hfile X kappa theta : share of predicted exceptions carried by the worst classes
Hf, X, kap = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]); th = None if sys.argv[4] == 'None' else float(sys.argv[4])
L = open(Hf).read().split('\n'); M, ns = map(int, L[0].split()); H = [tuple(map(int, x.split())) for x in L[1:] if x.strip()]
Ls = math.sqrt(math.log(X))
def p0(u):
    mu = kap * u / Ls
    return math.exp(-mu) if th is None else (th / (th + mu)) ** th
tot = sum(c * p0(u) for u, c in H); cc = 0; cm = 0
print('M=%d ns=%d  predicted exceptions per octave at X=%.2g: %.3g' % (M, ns, X, tot * X / M))
for u, c in sorted(H):
    cc += c; cm += c * p0(u)
    if cm / tot > 0.999: break
    print('  U<=%3d: classes %9d (%.2e of all)  mass share %.3f' % (u, cc, cc / M, cm / tot))
