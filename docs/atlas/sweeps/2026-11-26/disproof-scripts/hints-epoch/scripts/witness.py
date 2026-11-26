import json, re
idx = json.load(open('work/index.json')); sp = json.load(open('work/split.json'))
for cid in sp['dis']:
    a = min(idx[cid]['accepted'], key=lambda a: len(a['spec']))
    t = a['spec']
    # theorem statements
    ths = re.findall(r'(theorem\s+[^\n]*(?:\n(?!\s*\n)[^\n]*){0,4})', t)
    main = [x for x in ths if '¬' in x[:300]]
    cm = re.findall(r'/-(.*?)-/', t, re.S)
    key = [c for c in cm if re.search(r'false|counterexample|disprov|fails|witness', c, re.I)]
    print('=====', cid, len(t))
    for k in key[:2]: print('  C:', ' '.join(k.split())[:600])
    for m in main[:1]: print('  T:', ' '.join(m.split())[:400])
