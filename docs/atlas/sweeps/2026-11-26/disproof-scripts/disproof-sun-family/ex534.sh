#!/bin/bash
# A301534: primes p = 7 mod 12, scan [2^33, 1e11) in chunks of 2^33; stop file: stop534
th=$1; lo=8589934592; step=8589934592
while [ $lo -lt 100000000000 ]; do
  hi=$((lo+step)); [ $hi -gt 100000000000 ] && hi=100000000000
  [ -f stop534 ] && break
  if ! grep -qx "$lo" ex_a301534.done 2>/dev/null; then
    /usr/bin/time -f "a301534 $lo $hi %e s wall %U s user" ../src/hs3 ../specs/a301534.spec $lo $hi $th ex_a301534 2 12 7 1 2>> ex_a301534.time && echo $lo >> ex_a301534.done
  fi
  lo=$hi
done
echo FINISHED >> ex_a301534.time
