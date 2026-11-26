from fractions import Fraction as F
import sys
def alpha(S):
    s = max(S); full = (1<<s)-1
    # window bit j (0..s-1) = position x-1-j
    def ok(w):
        for j in range(s):
            if w>>j & 1:
                for d in S:
                    if j+d < s and (w >> (j+d)) & 1: return False
        return True
    V = [w for w in range(1<<s) if ok(w)]
    idx = {w:i for i,w in enumerate(V)}
    E = []
    for w in V:
        for b in (0,1):
            if b and any((w >> (d-1)) & 1 for d in S): continue
            nw = ((w << 1) | b) & full
            E.append((idx[w], idx[nw], b))
    n = len(V); NEG = None
    # Karp from a virtual source connected to all nodes with weight 0
    Dp = [[NEG]*n for _ in range(n+1)]
    Dp[0] = [0]*n
    for kk in range(1, n+1):
        prev, cur = Dp[kk-1], Dp[kk]
        for u, v, wgt in E:
            if prev[u] is not None and (cur[v] is None or prev[u]+wgt > cur[v]): cur[v] = prev[u]+wgt
    best = None
    for v in range(n):
        if Dp[n][v] is None: continue
        m = min(F(Dp[n][v]-Dp[kk][v], n-kk) for kk in range(n) if Dp[kk][v] is not None)
        if best is None or m > best: best = m
    return best, n
for S in [(1,3,4),(1,6,7),(1,8,9),(1,8,10),(1,8,11),(1,8,12),(1,8,13)]:
    print(S, *alpha(S)); sys.stdout.flush()
