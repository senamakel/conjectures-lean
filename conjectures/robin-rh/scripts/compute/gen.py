#!/usr/bin/env python3
"""Generate RobinCompute/Data.lean, Robin/Compute/Chunks/*.lean and Robin/Compute/Range.lean
from a states file (one line "B A T cov" per chunk boundary)."""
import sys, os
states_file, repo, x0 = sys.argv[1], sys.argv[2], int(sys.argv[3])
S = 2**34
st = [tuple(map(int, l.split())) for l in open(states_file) if l.strip()]
n = len(st) - 1
assert st[0] == (2, 0, 0, x0), st[0]
for i in range(n):
    assert st[i+1][0] == (i+1)*S, (i, st[i+1][0])
with open(os.path.join(repo, 'RobinCompute/Data.lean'), 'w') as f:
    f.write('import RobinCompute.Core\n\n')
    f.write('/-!\n# Chunk boundary states of the verified computation (generated)\n\n'
            'Produced by an untrusted run of the same code; every transition `s_i → s_{i+1}` is\n'
            're-checked by `native_decide` in `Robin/Compute/Chunks/`. Chunk `i` covers\n'
            f'`[max(2, i·2^34), (i+1)·2^34)`, `i < {n}`.\n-/\n\n')
    f.write('namespace RobinCompute\n\n')
    f.write(f'/-- Initial coverage `x0/XS ≤ log 10001`. -/\ndef x0 : Nat := {x0}\n\n')
    f.write(f'def nChunks : Nat := {n}\n\n')
    for i, (B, A, T, c) in enumerate(st):
        f.write(f'def s{i} : St := ⟨{B}, {A}, {T}, {c}⟩\n')
    f.write('\nend RobinCompute\n')
cd = os.path.join(repo, 'Robin/Compute/Chunks')
os.makedirs(cd, exist_ok=True)
for i in range(n):
    with open(os.path.join(cd, f'C{i:03d}.lean'), 'w') as f:
        f.write('import RobinCompute.Data\n\nnamespace RobinCompute\n\n')
        f.write(f'/-- Chunk {i} of the verified computation (`native_decide`). -/\n')
        f.write(f'theorem chunk_{i} : runChunk Gc s{i} {(i+1)*S} = s{i+1} := by native_decide\n\n')
        f.write('end RobinCompute\n')
with open(os.path.join(cd, 'Small.lean'), 'w') as f:
    f.write('import RobinCompute.Data\n\nnamespace RobinCompute\n\n')
    f.write('/-- The direct check for `5040 < n ≤ 10000` and the initial coverage bound '
            '(`native_decide`). -/\n')
    f.write('theorem small_ok : ((List.range\' 5041 4960).all directOK &&\n'
            '    decide (x0 * D ≤ XS * logLoNat 10001)) = true := by native_decide\n\n')
    f.write('end RobinCompute\n')
with open(os.path.join(repo, 'Robin/Compute/Chain.lean'), 'w') as f:
    f.write('import Robin.Compute.Run\n')
    for i in range(n):
        f.write(f'import Robin.Compute.Chunks.C{i:03d}\n')
    f.write('\n/-! # Chaining the chunks (generated) -/\n\nnamespace Robin.Compute\n\nopen RobinCompute\n\n')
    f.write(f'theorem valid_final : Valid x0 s{n} := by\n')
    f.write('  have v0 : Valid x0 s0 := valid_init x0\n')
    for i in range(n):
        f.write(f'  have v{i+1} : Valid x0 s{i+1} := by rw [← chunk_{i}]; exact runChunk_valid v{i} _\n')
    f.write(f'  exact v{n}\n\n')
    c = st[n][3]
    f.write(f'theorem final_cov : s{n}.cov = {c} := rfl\n\n')
    f.write('end Robin.Compute\n')
print('chunks', n, 'final cov/XS', st[n][3] / 2**20)
