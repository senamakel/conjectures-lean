import sys, math
# tail.py hist [o_lo o_hi]  -- geometric-tail ("near-miss") estimator.
# Per octave o: N_k(o) = #n in [2^o, 2^(o+1)) with exactly k represented sparse terms (k<=3).
# Pooled over the window: rho = (N1+N2)/(N2+N3) (geometric decay ratio of the low tail).
# Base level B(o) = N2(o)+N3(o) is fitted log-linearly in o over the window and extrapolated.
# Predicted N0(o) = B(o) * rho^2 * (N2+N3 share -> N0)  i.e. N0 = B * rho^2 / (1 + 1/rho) ... see below.
# With N_k = c * rho^k (geometric), N2+N3 = c rho^2 (1+rho), so N0 = (N2+N3)/(rho^2 (1+rho)).
f = sys.argv[1]; olo = int(sys.argv[2]) if len(sys.argv) > 2 else 22; ohi = int(sys.argv[3]) if len(sys.argv) > 3 else 31
obs = {}
for line in open(f):
    if line.startswith('oct'):
        p = line.split(); o = int(p[1]); c = list(map(int, p[2:6]))
        obs[o] = [a + b for a, b in zip(obs.get(o, [0, 0, 0, 0]), c)]
W = [o for o in range(olo, ohi + 1)]
S = [sum(obs.get(o, [0] * 4)[k] for o in W) for k in range(4)]
rho = (S[1] + S[2] + 0.5) / (S[2] + S[3] + 0.5)
# log-linear fit of B(o)
xs, ys = [], []
for o in W:
    b = obs.get(o, [0] * 4); xs.append(o); ys.append(math.log(b[2] + b[3] + 0.5))
n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
beta = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
alpha = my - beta * mx
def N0(o): return math.exp(alpha + beta * o) / (rho ** 2 * (1 + rho)) * rho ** 3 / rho ** 3 * (rho ** 2 / (1 + 0)) / (rho ** 2) * 1.0 if False else math.exp(alpha + beta * o) / ((1 + rho) * rho ** 2) * rho ** 0 * (rho ** 2) / (rho ** 2)
# N0 = c, N2+N3 = c(rho^-2 + rho^-3)?? careful: we model N_k = c * q^k with q = N_{k+1}/N_k > 1 (counts grow with k).
q = 1.0 / rho
def N0(o):
    B = math.exp(alpha + beta * o)          # = c (q^2 + q^3)
    return B / (q ** 2 + q ** 3)
obsN0 = sum(obs.get(o, [0] * 4)[0] for o in W)
fitN0 = sum(N0(o) for o in W)
tot = sum(N0(o) for o in range(33, 44))
print('%s window %d..%d: N0..N3 = %s  q=N(k+1)/N(k)=%.1f  growth/oct=%.2f  N0 in window pred %.3g obs %d  | pred (2^33,2^44): %.3g  | per-oct at 2^33: %.3g, at 2^43: %.3g'
      % (f, olo, ohi, S, q, math.exp(beta), fitN0, obsN0, tot, N0(33), N0(43)))
