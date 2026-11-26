import json, os, sys, re
root = sys.argv[1]; out = sys.argv[2]
runs = os.path.join(root, 'runs')
res = {}
for r in sorted(os.listdir(runs)):
    if 'oeis' not in r: continue
    rd = os.path.join(runs, r)
    for cid in os.listdir(rd):
        d = os.path.join(rd, cid)
        sj = os.path.join(d, 'scores.json')
        if not os.path.isfile(sj): continue
        try: s = json.load(open(sj))
        except Exception: continue
        v = s.get('proof_scorer', {}).get('value')
        ent = res.setdefault(cid, {'runs': {}, 'accepted': []})
        ent['runs'][r] = v
        if v == 'C':
            spec = os.path.join(d, 'Submission', 'Spec.lean')
            txt = open(spec, errors='replace').read() if os.path.isfile(spec) else ''
            # also collect other lean files sizes
            ent['accepted'].append({'run': r, 'spec': txt})
json.dump(res, open(out, 'w'))
print(len(res), sum(1 for v in res.values() if v['accepted']))
