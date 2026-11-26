import sys,glob,re
from fractions import Fraction
for n in sys.argv[1:]:
    rows=[]; T=0
    for f in sorted(glob.glob(f'runs/mso/n{n}_*.txt')):
        s=open(f).read()
        m=re.search(r'trees=(\d+) max mean=(\d+)/(\d+)=\S+ maximisers=(\d+) all_caterpillar=(\d) example=(.*)',s)
        if not m: print(n,'incomplete',f); break
        T+=int(m[1]); rows.append((Fraction(int(m[2]),int(m[3])),int(m[4]),int(m[5]),m[6].strip(),f))
    else:
        best=max(r[0] for r in rows); top=[r for r in rows if r[0]==best]
        print(n,'trees',T,'max',best,float(best),'maximisers',sum(r[1] for r in top),'all_cat',all(r[2] for r in top),top[0][3])
