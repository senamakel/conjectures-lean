#!/bin/bash
# usage: oeis_fetch.sh outname "query" maxpages
D=/tmp/claude-1000/-home-ubuntu-work-personal-conjectures/e6c3a6a3-3702-43d3-8640-5f8f102b5329/scratchpad/hunt-large/dl
UA="Mozilla/5.0 (X11; Linux x86_64; rv:128.0) Gecko/20100101 Firefox/128.0"
q=$(python3 -c "import urllib.parse,sys;print(urllib.parse.quote_plus(sys.argv[1]))" "$2")
: > $D/$1.txt
for ((i=0;i<$3;i++)); do
  curl -s -m 30 -A "$UA" "https://oeis.org/search?q=$q&fmt=text&start=$((i*10))" > $D/tmp_$1
  cat $D/tmp_$1 >> $D/$1.txt
  grep -q "^%I" $D/tmp_$1 || break
  sleep 1
done
rm -f $D/tmp_$1
grep -m1 "Showing" $D/$1.txt
