import re, sys
sys.path.insert(0, sys.argv[2])
from conjf import conj
from fractions import Fraction as F
txt = open(sys.argv[1]).read()
lines = txt.split('\\\\\\hline')
hdr = [int(x) for x in re.findall(r'\$(\d+)\$', lines[0].split('$k \\setminus i$')[1])]
for L in lines[1:]:
    m = re.match(r'\s*\$(\d+)\$\s*&(.*)', L, re.S)
    if not m or m.group(1) != '7': continue
    for i, c in zip(hdr, m.group(2).split('&')):
        k = 8+i; c=c.strip()
        red = 'red' in c
        a,b = re.findall(r'(\d+)\s*/\s*(\d+)', c)[0]; t = F(int(a),int(b))
        cf = conj(k); excl = k in {9,10,14,16,18,23,25,32}
        flag = '' if t == cf else ('TABLE>CONJ' if t > cf else 'TABLE<CONJ')
        print(k, k%9, 'red' if red else 'black', t, cf, 'excluded' if excl else '', flag)
