import re, sys
for fn in sys.argv[1:]:
    lines = open(fn).read().split('\\\\\\hline')
    hdr = [int(x) for x in re.findall(r'\$(\d+)\$', lines[0].split('$k \\setminus i$')[1])]
    for L in lines[1:]:
        m = re.match(r'\s*\$(\d+)\$\s*&(.*)', L, re.S)
        if not m or m.group(1) != '7': continue
        cells = m.group(2).split('&')
        print(fn.split('/')[-1], 'header i range', hdr[0], hdr[-1])
        for i, c in zip(hdr, cells):
            c = c.strip()
            if c: print(f"  S={{1,8,{8+i}}} : {c}")
