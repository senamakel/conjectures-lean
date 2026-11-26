"""Exhaustive check of curated conjectures on all connected graphs of order n (geng -c n res/mod).
usage: exh_c2.py GENG n res mod   -> prints max slack per conjecture (absolute LHS-RHS) and argmax graph6."""
import sys, subprocess
import numpy as np

geng, n, res, mod = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
out = subprocess.run([geng, '-cq', str(n), f'{res}/{mod}'], capture_output=True, check=True).stdout
lines = out.split(b'\n')[:-1]
nbits = n * (n - 1) // 2; nch = (nbits + 5) // 6
iu = [(i, j) for j in range(n) for i in range(j)]
I = np.array([p[0] for p in iu]); J = np.array([p[1] for p in iu])
best = {}
CH = 200000
for s in range(0, len(lines), CH):
    L6 = lines[s:s + CH]; N = len(L6)
    raw = np.frombuffer(b''.join(l[1:1 + nch] for l in L6), dtype=np.uint8).reshape(N, nch) - 63
    bits = np.unpackbits(raw[:, :, None], axis=2)[:, :, 2:].reshape(N, -1)[:, :nbits]
    A = np.zeros((N, n, n)); A[:, I, J] = bits; A[:, J, I] = bits
    deg = A.sum(2); Lp = -A.copy(); Lp[:, np.arange(n), np.arange(n)] = deg
    ea = np.linalg.eigvalsh(A); el = np.linalg.eigvalsh(Lp)
    l1, l2 = ea[:, -1], ea[:, -2]; mu1, mu2 = el[:, -1], el[:, -2]; m = deg.sum(1) / 2
    rk = (np.abs(ea) > 1e-8).sum(1)
    tests = {
        'C2 l2-(mu1-2)': l2 - (mu1 - 2),
        'C6ii 4l2+1-mu2^2': 4 * l2 + 1 - mu2 ** 2,
        'C6iii 4l2+8-mu1^2': 4 * l2 + 8 - mu1 ** 2,
        'C4 l1-(R+mu2) [R omitted]': None,
        'C5 mu2+rk-2m': mu2 + rk - 2 * m,
        'C1s1 l1^2+(l2+1)^2-2m': l1 ** 2 + (l2 + 1) ** 2 - 2 * m,
        'C1s2 l1(l2+1)-m': l1 * (l2 + 1) - m,
    }
    for k, v in tests.items():
        if v is None: continue
        i = int(v.argmax())
        if k not in best or v[i] > best[k][0]: best[k] = (float(v[i]), L6[i].decode())
print(n, res, mod, len(lines), best)
