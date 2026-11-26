#!/usr/bin/env python3
"""Generate the native_decide chunk files and their assembly modules.

Binary Goldbach: even m in [6, 6 + NB * WB), WB = 2 * K * N, one chunk per WB.
Ladder: y in [2 * 10^12, 10^20], one chunk per 10^18.
Run from the repository root: python3 -I scripts/gen_chunks.py
"""
import os

P, K, N = 9999, 500000, 10000          # small primes <= P, segments of K evens, N segments
WB = 2 * K * N                          # 10^10 even-number span per chunk
NB = 200                                # covers [6, 6 + 2*10^12)
A0 = 6
G = 2 * 10**12 - 4                      # ladder gap bound
LO0, STEP, NL = 2 * 10**12, 10**18, 100 # ladder covers [2*10^12, 10^20]

root = os.path.join("Goldbach", "Compute")
os.makedirs(os.path.join(root, "BinaryChunks"), exist_ok=True)
os.makedirs(os.path.join(root, "LadderChunks"), exist_ok=True)

NOTE = """This is evaluated by `native_decide`, which adds one auxiliary axiom
(`{name}._native.native_decide.ax_*`) asserting that the compiled evaluation of the checker
agrees with its definition. The checker and its soundness are proved without it."""

for j in range(NB):
    name = f"binary_chunk_{j}"
    with open(os.path.join(root, "BinaryChunks", f"B{j:03d}.lean"), "w") as f:
        f.write(f"""import GoldbachCheck

namespace Goldbach.Check

/-- Binary Goldbach chunk {j}: every even `m` in `[{A0} + {j} * {WB}, {A0} + {j + 1} * {WB})` is
`p + q` with `p ≤ {P}` an odd prime.

{NOTE.format(name=name)} -/
theorem {name} : goldbachChunk {P} ({A0} + {j} * {WB}) {K} {N} = true := by
  native_decide

end Goldbach.Check
""")

def ladder_range(j):
    lo = LO0 if j == 0 else j * STEP
    return lo, (j + 1) * STEP

for j in range(NL):
    lo, hi = ladder_range(j)
    name = f"ladder_chunk_{j}"
    with open(os.path.join(root, "LadderChunks", f"L{j:03d}.lean"), "w") as f:
        f.write(f"""import GoldbachCheck

namespace Goldbach.Check

/-- Ladder chunk {j}: a chain of Pocklington-certified primes with gaps `≤ {G}` covering
`[{lo}, {hi}]`.

{NOTE.format(name=name)} -/
theorem {name} : ladderCover {G} {lo} {hi} = true := by
  native_decide

end Goldbach.Check
""")

# Assembly modules
with open(os.path.join(root, "BinaryAll.lean"), "w") as f:
    f.write("import Goldbach.Compute.Binary\n")
    for j in range(NB):
        f.write(f"import Goldbach.Compute.BinaryChunks.B{j:03d}\n")
    f.write(f"""
/-!
# Binary Goldbach up to `2·10¹²` (verified computation)

The {NB} chunks `binary_chunk_j` (files `BinaryChunks/B*.lean`, built in parallel) each check
`goldbachChunk {P} ({A0} + j * {WB}) {K} {N} = true` by `native_decide`.
-/

namespace Goldbach.Check

theorem binary_chunks_ok : ∀ j < {NB}, goldbachChunk {P} ({A0} + j * {WB}) {K} {N} = true := by
  intro j hj
  interval_cases j
""")
    for j in range(NB):
        f.write(f"  · exact binary_chunk_{j}\n")
    f.write("\nend Goldbach.Check\n")

with open(os.path.join(root, "LadderAll.lean"), "w") as f:
    f.write("import Goldbach.Compute.Ladder\n")
    for j in range(NL):
        f.write(f"import Goldbach.Compute.LadderChunks.L{j:03d}\n")
    f.write(f"""
/-!
# A prime ladder with gaps `≤ {G}` from `2·10¹²` to `10²⁰` (verified computation)

The {NL} chunks `ladder_chunk_j` (files `LadderChunks/L*.lean`) each check
`ladderCover {G} lo_j hi_j = true` by `native_decide`, with `lo_0 = {LO0}`,
`lo_j = j * {STEP}` for `j ≥ 1` and `hi_j = (j + 1) * {STEP}`.
-/

namespace Goldbach.Check

theorem ladder_chunks_ok : ∀ j < {NL},
    ladderCover {G} (if j = 0 then {LO0} else j * {STEP}) ((j + 1) * {STEP}) = true := by
  intro j hj
  interval_cases j
""")
    for j in range(NL):
        f.write(f"  · exact ladder_chunk_{j}\n")
    f.write("\nend Goldbach.Check\n")
print("ok")
