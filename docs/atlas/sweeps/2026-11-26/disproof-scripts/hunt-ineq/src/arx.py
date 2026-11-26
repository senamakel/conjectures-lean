import re,sys,urllib.request,urllib.parse,time,json
def q(query,n=60):
    url="https://export.arxiv.org/api/query?"+urllib.parse.urlencode({"search_query":query,"sortBy":"submittedDate","sortOrder":"descending","max_results":n})
    t=urllib.request.urlopen(url,timeout=90).read().decode()
    out=[]
    for e in t.split('<entry>')[1:]:
        g=lambda p:re.search(p,e,re.S).group(1)
        out.append(dict(id=g(r'<id>(.*?)</id>').split('/abs/')[-1],date=g(r'<published>(.*?)</published>')[:10],title=' '.join(g(r'<title>(.*?)</title>').split()),abs=' '.join(g(r'<summary>(.*?)</summary>').split()),cat=re.findall(r'term="([^"]+)"',e)))
    return out
if __name__=="__main__":
    seen=set()
    for query in sys.argv[1:]:
        for r in q(query):
            if r['id'] in seen or r['date']<'2022': continue
            seen.add(r['id'])
            print(f"{r['date']} {r['id']} [{','.join(c for c in r['cat'] if '.' in c)[:30]}] {r['title'][:100]}")
            a=r['abs']; i=a.lower().find('conjectur'); print('    ',a[max(0,i-200):i+250])
        time.sleep(3)
