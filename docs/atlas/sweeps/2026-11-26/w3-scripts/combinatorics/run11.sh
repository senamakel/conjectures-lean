#!/bin/bash
cd /tmp/claude-1000/-home-ubuntu-work-personal-conjectures/80f083f8-5ab0-487d-92fb-ea9d3923a16c/scratchpad/w3c
for i in $(seq 0 47); do (bin/geng -cq 11 $i/48 | bin/wow2 > runs/w11.$i.out 2> runs/w11.$i.err) & done; wait
echo done > runs/w11.done
