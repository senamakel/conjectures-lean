#!/bin/bash
# chunk i: [max(2, i*2^34), (i+1)*2^34), i = 0..622
cd "$(dirname "$0")"
S=$((2**34))
for i in $(seq 0 622); do
  B0=$((i*S)); [ $i -eq 0 ] && B0=2
  B1=$(((i+1)*S))
  f=out/c$(printf %04d $i)
  [ -f $f ] || echo "$B0 $B1 $f"
done | xargs -P 60 -n 3 nice -n 10 ./pass1.bin
echo PASS1_DONE
