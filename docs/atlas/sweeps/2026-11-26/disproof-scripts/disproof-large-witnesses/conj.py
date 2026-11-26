import sys,re,collections
# print A-number, name, and conjecture comment lines from OEIS text dumps
seen=set()
for fn in sys.argv[1:]:
    ent=collections.OrderedDict()
    for line in open(fn,errors='replace'):
        m=re.match(r'%(\w) (A\d{6}) ?(.*)',line)
        if not m: continue
        t,a,s=m.groups()
        ent.setdefault(a,{'N':'','C':[]})
        if t=='N': ent[a]['N']=s
        if t in 'CF' and re.search(r'onjectur|no other|no more|finite',s): ent[a]['C'].append(s)
    for a,e in ent.items():
        if a in seen or not e['C']: continue
        seen.add(a)
        print(a, e['N'][:160])
        for c in e['C'][:4]: print('    *', c[:400])
