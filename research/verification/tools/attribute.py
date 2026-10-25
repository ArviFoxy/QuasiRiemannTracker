#!/usr/bin/env python3
"""Attribute a lean4export ndjson file to namespaces.
For each declaration: bytes of all lines emitted since the previous declaration (the new names,
levels and expressions it introduced) plus its own line. Group by namespace prefix."""
import json, sys, collections, re

path = sys.argv[1]
names = {0: ''}
DECL_KEYS = ('axiom', 'def', 'opaque', 'thm', 'quot', 'inductive')
def full(i):
    return names.get(i, '?')

MOD = {}
if len(sys.argv) > 2:
    for line in open(sys.argv[2]):
        m, _, c = line.rstrip('\n').partition('\t')
        MOD[c] = m

def bucket_mod(m):
    for pre, lab in [('Submissions.openai_baseline', 'openai_baseline'),
                     ('Submissions.hailey_collet', 'hailey_collet'),
                     ('Submissions.arvi_', 'arvi (ours)'),
                     ('Submissions.', 'Submissions.other'),
                     ('Candidate', 'Candidate'), ('Mathlib', 'Mathlib'),
                     ('PrimeNumberTheoremAnd', 'PrimeNumberTheoremAnd'),
                     ('Init', 'Lean core'), ('Std', 'Lean core'), ('Lean', 'Lean core'), ('Batteries', 'Batteries')]:
        if m.startswith(pre): return lab
    return 'other:' + m.split('.')[0]

def bucket(n):
    if MOD:
        return bucket_mod(MOD.get(n, '<unknown>'))
    if n.startswith('Submissions.openai_baseline'): return 'openai_baseline'
    if n.startswith('Submissions.hailey_collet'): return 'hailey_collet'
    if n.startswith('Submissions.arvi_'): return 'arvi (ours)'
    if n.startswith('Submissions.'): return 'Submissions.other:' + n.split('.')[1]
    if n.startswith('Candidate'): return 'Candidate'
    top = n.split('.')[0]
    if top in ('Mathlib',): return 'Mathlib'
    return 'other:' + top

DUMP = open(sys.argv[3], 'w') if len(sys.argv) > 3 else open('/dev/null', 'w')
pending = 0
stats = collections.defaultdict(lambda: [0, 0])   # bucket -> [decls, bytes]
top_decls = []
kinds = collections.Counter()
with open(path, 'rb') as f:
    for raw in f:
        L = len(raw)
        if raw.startswith(b'{"in"') or b'"in":' in raw[:12]:
            o = json.loads(raw)
            i = o['in']
            if 'str' in o: names[i] = (names[o['str']['pre']] + '.' if o['str']['pre'] else '') + o['str']['str']
            elif 'num' in o: names[i] = (names[o['num']['pre']] + '.' if o['num']['pre'] else '') + str(o['num']['i'])
            pending += L
            continue
        head = raw[:40]
        if any(('"%s"' % k).encode() in head for k in DECL_KEYS):
            o = json.loads(raw)
            k = next(k for k in DECL_KEYS if k in o)
            kinds[k] += 1
            d = o[k]
            if k == 'inductive':
                nm = full(d['types'][0]['name']) if 'types' in d and d['types'] else '?'
            elif k == 'quot':
                nm = 'Quot'
            else:
                nm = full(d['name'])
            # Mathlib declarations are not under a Mathlib namespace; classify by known prefixes later
            b = bucket(nm)
            cost = pending + L
            stats[b][0] += 1; stats[b][1] += cost
            top_decls.append((cost, nm))
            DUMP.write(f'{cost}\t{b}\t{nm}\n')
            if len(top_decls) > 4000:
                top_decls.sort(reverse=True); del top_decls[400:]
            pending = 0
        else:
            pending += L
top_decls.sort(reverse=True)
tot = sum(v[1] for v in stats.values())
print('kinds:', dict(kinds))
print(f'total bytes attributed {tot/1e6:.1f} MB, declarations {sum(v[0] for v in stats.values())}')
for b, (n, by) in sorted(stats.items(), key=lambda kv: -kv[1][1])[:40]:
    print(f'{b:45s} decls {n:7d}  MB {by/1e6:9.1f}  ({100*by/tot:5.1f}%)')
print('--- 60 largest declarations (bytes introduced) ---')
for c, nm in top_decls[:60]:
    print(f'{c/1e6:8.2f} MB  {nm}')
