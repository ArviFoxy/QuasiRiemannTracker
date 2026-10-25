#!/usr/bin/env python3
"""Low-memory per-declaration attribution of a lean4export ndjson file.
Names are stored as (prefix index, interned component) in arrays; full names are built only
for declarations. Output: bytes<TAB>module<TAB>name for each declaration."""
import json, sys, re
from array import array
path, modmap, out = sys.argv[1], sys.argv[2], sys.argv[3]
MOD = {}
for line in open(modmap):
    m, _, c = line.rstrip('\n').partition('\t')
    MOD[c] = m
pre = array('q', [0]); comp = ['']
intern = {}
def full(i):
    parts = []
    while i:
        parts.append(comp[i]); i = pre[i]
    return '.'.join(reversed(parts))
DECL = (b'"axiom"', b'"def"', b'"opaque"', b'"thm"', b'"quot"', b'"inductive"')
pending = 0
o_out = open(out, 'w')
with open(path, 'rb') as f:
    for raw in f:
        L = len(raw)
        if raw.startswith(b'{"in"'):
            o = json.loads(raw); i = o['in']
            if 'str' in o:
                p, s = o['str']['pre'], o['str']['str']
            elif 'num' in o:
                p, s = o['num']['pre'], str(o['num']['i'])
            else:
                pending += L; continue
            s = intern.setdefault(s, s)
            while len(pre) <= i:
                pre.append(0); comp.append('')
            pre[i] = p; comp[i] = s
            pending += L; continue
        head = raw[:40]
        if any(k in head for k in DECL):
            o = json.loads(raw)
            k = next(k for k in ('axiom','def','opaque','thm','quot','inductive') if k in o)
            d = o[k]
            if k == 'inductive':
                nm = full(d['types'][0]['name']) if d.get('types') else '?'
            elif k == 'quot':
                nm = 'Quot'
            else:
                nm = full(d['name'])
            o_out.write(f'{pending+L}\t{MOD.get(nm,"<unknown>")}\t{nm}\n')
            pending = 0
        else:
            pending += L
o_out.close()
