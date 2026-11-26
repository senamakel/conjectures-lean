import re,sys,os,json,glob
root=sys.argv[1]; out=sys.argv[2]
decls=[]
for f in sorted(glob.glob(root+'/FormalConjectures/**/*.lean',recursive=True)):
    if '/ErdosProblems/' in f: continue
    txt=open(f).read()
    # find attribute blocks with research open
    for m in re.finditer(r'@\[category research open[^\]]*\]\s*\n(theorem|lemma|def)\s+(\S+)',txt):
        start=m.start()
        # statement: from m.start to ':= by' or ':= sorry'
        end=txt.find(':= by',m.end())
        e2=txt.find(':= sorry',m.end())
        cand=[x for x in (end,e2) if x!=-1]
        end=min(cand) if cand else m.end()+400
        # docstring before
        ds=txt.rfind('/--',0,start); dse=txt.find('-/',ds)
        doc=txt[ds:dse+2] if ds!=-1 and dse<start and start-dse<5 else ''
        decls.append(dict(file=f[len(root)+1:],name=m.group(2),stmt=txt[m.end(2)+0:end].strip(),doc=doc,size=end-m.end()))
json.dump(decls,open(out,'w'),indent=0)
print(len(decls))
