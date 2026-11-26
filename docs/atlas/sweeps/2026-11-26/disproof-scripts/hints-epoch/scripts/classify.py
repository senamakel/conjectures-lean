import json, re, sys
idx = json.load(open('work/index.json')); cj = json.load(open('work/conjectures.json'))
dis, pro = [], []
for cid, e in sorted(idx.items()):
    if not e['accepted']: continue
    flags = []
    for a in e['accepted']:
        t = a['spec']
        # find theorem statements
        m = re.findall(r'theorem\s+(\S+)\s*:\s*(¬|\(¬)', t)
        flags.append(bool(m) or bool(re.search(r'theorem\s+\S*(disproof|false|counterexample|not)\S*', t, re.I)))
    isd = sum(flags) > len(flags)/2
    (dis if isd else pro).append(cid)
print(len(dis), len(pro))
json.dump({'dis': dis, 'pro': pro}, open('work/split.json','w'))
for c in dis:
    print(c, '|', cj[c]['proposer'], cj[c]['proposed_date'], '|', cj[c]['conjecture'][:150].replace('\n',' '))
