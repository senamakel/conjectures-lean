import sys, os, math, subprocess
# fit.py spec calhist comps [oct_fit_lo oct_fit_hi] [known_exceptions_file]
# Model: n in octave [2^o, 2^(o+1)), class a mod M with U(a) locally unblocked sparse terms;
# r(n) ~ NegBin(mean = kappa*U/sqrt(ln X), shape theta)   (theta -> inf: Poisson).
# Fit (kappa, theta) to observed counts N_1..N_3 per octave in the fit window, then predict N_0.
HERE = os.path.dirname(os.path.abspath(__file__))
spec, calhist, comps = sys.argv[1], sys.argv[2], sys.argv[3]
olo = int(sys.argv[4]) if len(sys.argv) > 4 else 26
ohi = int(sys.argv[5]) if len(sys.argv) > 5 else 31
obs = {}
for line in open(calhist):
    if line.startswith('oct'):
        p = line.split(); o = int(p[1]); c = list(map(int, p[2:]))
        obs[o] = [a + b for a, b in zip(obs.get(o, [0] * len(c)), c)]
Hcache = {}
def H(o):
    if o in Hcache: return Hcache[o]
    X = 2.0 ** o * 1.5
    tmp = '/tmp/claude-1000/-home-ubuntu-work-personal-conjectures/e6c3a6a3-3702-43d3-8640-5f8f102b5329/scratchpad/hunt-sun/work/H_%d_%d.txt' % (os.getpid(), o)
    subprocess.run([os.path.join(HERE, 'model'), spec, str(X), comps, '/dev/null', '0', tmp], capture_output=True, check=True)
    L = open(tmp).read().split('\n'); M, ns = map(int, L[0].split())
    h = [(int(a), int(b) / M) for a, b in (x.split() for x in L[1:] if x.strip())]
    os.remove(tmp); Hcache[o] = h; return h
def lpmf(k, mu, th):
    if th is None:
        return -mu + k * math.log(mu) - math.lgamma(k + 1) if mu > 0 else (0.0 if k == 0 else -1e300)
    return (math.lgamma(k + th) - math.lgamma(k + 1) - math.lgamma(th) + th * math.log(th / (th + mu))
            + (k * math.log(mu / (th + mu)) if k else 0.0))
def pred(o, k, kap, th):
    X = 2.0 ** o; L = math.sqrt(math.log(1.5 * X)); s = 0.0
    for u, w in H(o):
        mu = kap * u / L
        if mu <= 0: s += w * (1.0 if k == 0 else 0.0); continue
        s += w * math.exp(lpmf(k, mu, th))
    return X * s
def loss(kap, th):
    e = 0.0
    for o in range(olo, ohi + 1):
        if o not in obs: continue
        for k in (1, 2, 3):
            if k >= len(obs[o]): continue
            y = obs[o][k]; p = pred(o, k, kap, th)
            e += (math.log(y + 0.5) - math.log(p + 0.5)) ** 2
    return e
best = None
for th in [None, 64, 32, 16, 8, 4, 2, 1]:
    for kap in [x / 20 for x in range(4, 100)]:
        l = loss(kap, th)
        if best is None or l < best[0]: best = (l, kap, th)
l, kap, th = best
print('fit: kappa=%.2f theta=%s loss=%.3f  (octaves %d..%d)' % (kap, th, l, olo, ohi))
for o in range(olo, ohi + 1):
    if o in obs: print('  oct %d obs %s pred %s' % (o, obs[o][:4], ['%.1f' % pred(o, k, kap, th) for k in range(4)]))
tot = 0.0
for o in range(ohi + 1, 44):
    p0 = pred(o, 0, kap, th); tot += p0 if o >= 33 else 0
    print('  oct %d [%.2e,%.2e) predicted exceptions %.3g' % (o, 2.0 ** o, 2.0 ** (o + 1), p0))
print('TOTAL predicted exceptions in [2^33, 2^44) ~ (8.6e9, 1.76e13): %.3g' % tot)
p_obs = sum(pred(o, 0, kap, th) for o in range(olo, ohi + 1))
print('predicted exceptions in fit window: %.3g ; observed: %s' % (p_obs, sum(obs[o][0] for o in range(olo, ohi + 1) if o in obs)))
