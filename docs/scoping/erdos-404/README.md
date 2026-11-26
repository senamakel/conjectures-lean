# Erdős #404(ii) spike: code and data

See `REPORT.md` for the findings. Everything here is exact integer arithmetic, except `count.c`, which uses floating-point probabilities. The programs are single-threaded; run them with `nice -n 19` and `ulimit -v 4000000`.

```
gcc -O2 -o cover cover.c
gcc -O2 -o fwd fwd.c
gcc -O2 -o count count.c -lm
gcc -O2 -DREAL=float -DMAXM=250000000ULL -o count_f count.c -lm   # p=5, k=12 (about 2 GB)
```

| Program | What it computes |
|---|---|
| `cover.c` | The exact set of subset sums mod p^D, computed top-down with a "periodic window" (REPORT §3.1). `cover block p N H [extra]` takes the elements (N+j)!/N!, 0≤j<H, modulo p^{v_p((N+H)!/N!)+extra}. `cover tail p D nmin` takes the elements n! for n ≥ nmin with v_p(n!) < D, modulo p^D, and also reports whether −1 is reached (the a=1 question). Environment variables: `WCAP` (window cap, guarded at ≤1 GB per bitset), `EXCLOG=file` (log of every excursion: top, bottom, width, skipped levels), `VERBOSE=1`, `DUMP=1` (list missing residues when the window is small). |
| `brute_check.py` | Independent dense Python big-int DP for the same two modes, used to validate `cover.c` on small cases. |
| `fwd.c` | Forward carry DP for a fixed start a and precision K: `fwd p a K`. It gives exact f(a,p) when the set of states dies (reproduces Kitamura's values) and the number of surviving states block by block. |
| `count.c` | Multiplicity profile: `count p nmin kmax`. For each k it reports the normalised count p^k·P(Σ ε_n n! ≡ r mod p^k) at r=−1, together with its min and max over r and the fraction of residues with count zero. |

## Rerun the result files (`results/`)

```
# clean blocks at N=0 and cross-checks (seconds)
for a in "3 0 9" "3 0 27" "5 0 25" "5 0 125" "5 0 625" "7 0 49" "7 0 343" "2 0 8"; do ./cover block ${=a}; done
python3 -I brute_check.py block 3 0 27; python3 -I brute_check.py tail 5 10 2
DUMP=1 ./cover block 3 0 9          # missing residues 68, 77 (mod 81)

# full tails from n=2 (tail_N2*.txt, excursion logs); about 1 minute in total
EXCLOG=results/exc_p5_D5000.log WCAP=14 ./cover tail 5 5000 2
EXCLOG=results/exc_p7_D40000.log WCAP=11 ./cover tail 7 40000 2
EXCLOG=results/exc_p11_D100000.log WCAP=9 ./cover tail 11 100000 2
EXCLOG=results/exc_p13_D200000.log WCAP=8 ./cover tail 13 200000 2

# clean blocks at many positions (clean_blocks_all_c.txt): loop over c in `cover block p c*p^E p^E`
# surplus digits (clean_block_surplus.txt): `cover block p 0 p^E s` for s = 0,1,2,...

# multiplicity profiles (multiplicity.txt), a few minutes
for a in "2 2 25" "3 2 16" "5 2 11" "7 2 9" "11 2 7" "13 2 6"; do ./count ${=a}; done
./count_f 5 2 12

# forward DP (fwd_*.txt) and exact values
./fwd 5 1 12; ./fwd 3 39 27; ./fwd 5 236 63; ./fwd 7 42 9; ./fwd 2 4 8
```

The large excursion logs are gzipped. `excursion_summary.txt` tabulates them.
