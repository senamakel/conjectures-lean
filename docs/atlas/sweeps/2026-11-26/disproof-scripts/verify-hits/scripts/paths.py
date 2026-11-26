import re, sys
t = open(sys.argv[1]).read()
for m in re.finditer(r'<path([^>]*)>', t):
    a = m.group(1)
    d = re.search(r' d="([^"]*)"', a).group(1)
    st = re.search(r'stroke="([^"]*)"', a); tr = re.search(r'transform="([^"]*)"', a)
    nums = re.findall(r'[-\d.]+ [-\d.]+', d)
    if len(nums) > 3:
        print(st.group(1) if st else None, tr.group(1) if tr else None, len(nums), d[:300])
