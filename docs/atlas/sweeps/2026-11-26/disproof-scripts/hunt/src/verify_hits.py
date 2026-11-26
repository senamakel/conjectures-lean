"""Second, independent check of corpus hits.
- statement taken from the infix column `enonce` (not the prefix formula used by the search);
- eigenvalues by mpmath (60 digits, Jacobi via mp.eigsy), rank of A exactly over Q;
- radius/diameter by a separate BFS.  Binder statements (max over vertices/edges) are skipped.
usage: verify_hits.py HITS.jsonl  (lines with id, stmt, n, edges)"""
import sys, json, re
from fractions import Fraction
import mpmath as mp
mp.mp.dps = 60

def rank_exact(A):
    M = [[Fraction(x) for x in r] for r in A]; n = len(M); r = 0
    for c in range(n):
        p = next((i for i in range(r, n) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(n):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r

def inv(n, E):
    A = [[0] * n for _ in range(n)]
    for a, b in E: A[a][b] = A[b][a] = 1
    deg = [sum(r) for r in A]
    L = [[(deg[i] if i == j else 0) - A[i][j] for j in range(n)] for i in range(n)]
    ea = sorted(mp.eigsy(mp.matrix(A), eigvals_only=True), reverse=True)
    el = sorted(mp.eigsy(mp.matrix(L), eigvals_only=True), reverse=True)
    ecc = []
    for s in range(n):
        d = {s: 0}; q = [s]
        for u in q:
            for w in range(n):
                if A[u][w] and w not in d: d[w] = d[u] + 1; q.append(w)
        assert len(d) == n, 'disconnected'
        ecc.append(max(d.values()))
    m = sum(deg) // 2
    R = sum(1 / mp.sqrt(deg[a] * deg[b]) for a, b in E)
    return {'λ1': ea[0], 'λ2': ea[1], 'μ1': el[0], 'μ2': el[1], 'rank(A)': mp.mpf(rank_exact(A)),
            'rank(L)': mp.mpf(n - 1), 'tr(A)': mp.mpf(0), 'tr(L)': mp.mpf(2 * m), 'Randić': R,
            'rad': mp.mpf(min(ecc)), 'diam': mp.mpf(max(ecc))}

def evaluate(stmt, I):
    if 'max' in stmt or 'deg' in stmt or 'temp' in stmt or 'w(' in stmt: return None
    lhs, rhs = stmt.split('≤')
    def e(s):
        s = s.replace('^', '**')
        names = sorted(I, key=len, reverse=True)
        env = {}
        for k, nm in enumerate(names):
            tok = f'_v{k}'; s = s.replace(nm, tok); env[tok] = I[nm]
        env.update(sqrt=mp.sqrt, log=mp.log)
        return eval(s, {'__builtins__': {}}, env)
    return e(lhs), e(rhs)

if __name__ == '__main__':
    for line in open(sys.argv[1]):
        d = json.loads(line)
        I = inv(d['n'], d['edges'])
        r = evaluate(d['stmt'], I)
        if r is None: print(d['id'], 'binder statement: skipped'); continue
        a, b = r
        print(d['id'], d['stmt'], '| n =', d['n'], '| LHS - RHS =', mp.nstr(a - b, 12),
              '| CONFIRMED' if a - b > mp.mpf('1e-30') else '| NOT confirmed')
