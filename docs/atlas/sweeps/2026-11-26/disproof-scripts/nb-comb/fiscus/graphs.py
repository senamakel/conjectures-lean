# emit closed-neighbourhood masks for named graphs: grid a b | torus a b | cylinder a b (P_a x C_b) | path n | cycle n | kneser m k
import sys, itertools
def out(n, adj):
    print(n); print(" ".join(str((1 << v) | sum(1 << u for u in adj[v])) for v in range(n)))
kind = sys.argv[1]; args = list(map(int, sys.argv[2:]))
if kind in ("grid", "torus", "cyl"):
    a, b = args; idx = lambda i, j: i*b + j; adj = [set() for _ in range(a*b)]
    for i in range(a):
        for j in range(b):
            nb = []
            if kind == "torus":
                nb = [((i+1) % a, j), ((i-1) % a, j), (i, (j+1) % b), (i, (j-1) % b)]
            elif kind == "cyl":   # P_a x C_b
                nb = [(i+1, j), (i-1, j), (i, (j+1) % b), (i, (j-1) % b)]
            else:
                nb = [(i+1, j), (i-1, j), (i, j+1), (i, j-1)]
            for (x, y) in nb:
                if 0 <= x < a and 0 <= y < b and (x, y) != (i, j): adj[idx(i, j)].add(idx(x, y))
    out(a*b, adj)
elif kind == "path":
    n, = args; out(n, [set(u for u in (v-1, v+1) if 0 <= u < n) for v in range(n)])
elif kind == "cycle":
    n, = args; out(n, [{(v-1) % n, (v+1) % n} for v in range(n)])
elif kind == "kneser":
    m, k = args; V = list(itertools.combinations(range(m), k))
    out(len(V), [set(j for j, B in enumerate(V) if not set(A) & set(B)) for A in V])
