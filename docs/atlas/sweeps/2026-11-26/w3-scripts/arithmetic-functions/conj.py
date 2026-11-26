import json,sys,re
for f in sys.argv[1:]:
    try: d=json.load(open(f))
    except Exception as e: print(f,"ERR",e); continue
    if isinstance(d,dict): d=d.get('results') or []
    for r in d or []:
        print("=====",r.get('number'),r.get('name'))
        for key in ('comment','formula','example'):
            for line in r.get(key,[]) or []:
                if re.search(r'onjectur|open|question|unknown|Is it true|for all n >|for n >',line,re.I):
                    print(key[:3],"|",line[:400])
