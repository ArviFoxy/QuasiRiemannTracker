import os, re, sys
root = sys.argv[1]
PKG = 'Submissions.repeated_marks_20261024'
mods = {}
for d, _, fs in os.walk(os.path.join(root, 'Fork')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f)
            m = os.path.relpath(p, root)[:-5].replace('/', '.')
            deps = [l.split()[1][len(PKG)+1:] for l in open(p) if l.startswith('import ' + PKG + '.Fork.')]
            mods[m] = deps
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in mods.get(m, []): visit(d)
    order.append(m)
for m in sorted(mods): visit(m)
print('\n'.join(x.replace('.', '/') for x in order))
