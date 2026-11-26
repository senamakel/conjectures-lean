import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from arx import q
seen=set()
for query in sys.argv[2:]:
    for r in q(query,int(sys.argv[1])):
        if r['id'] in seen or r['date']<'2022': continue
        seen.add(r['id'])
        a=r['abs']; i=a.lower().find('conjectur')
        print(f"{r['date']} {r['id']} [{','.join(sorted(set(c for c in r['cat'] if '.' in c)))[:40]}] {r['title'][:110]}\n     {a[max(0,i-250):i+300]}")
    time.sleep(3)
