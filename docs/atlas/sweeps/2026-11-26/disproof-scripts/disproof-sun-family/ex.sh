#!/bin/bash
# exhaustive scan of statement $1 over [1e10, 1e12) in chunks of 5e10, $2 threads; resumes from ex_$1.done
s=$1; th=$2
for i in $(seq 0 19); do
  lo=$(python3 -c "print(int(1e10+$i*5e10))"); hi=$(python3 -c "print(int(1e10+($i+1)*5e10))")
  [ $hi -gt 1000000000000 ] && hi=1000000000000
  [ $lo -ge $hi ] && break
  grep -qx "$lo" ex_$s.done 2>/dev/null && continue
  /usr/bin/time -f "$s $lo $hi %e s wall %U s user" ../src/hs2_26_24 ../specs/$s.spec $lo $hi $th ex_$s 2 2>> ex_$s.time && echo $lo >> ex_$s.done
done
echo FINISHED >> ex_$s.time
