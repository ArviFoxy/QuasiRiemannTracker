"""Compact markdown tables for the README from results/B_*.json (rows = B, columns = m).

usage: python3 -I compact_B.py results/B_main.json
cell = actual (multiplicative-surrogate mean); then rows with N^3/R, number of terms, exact diagonal, full-family control.
"""
import sys, json, math
sys.dont_write_bytecode = True
import numpy as np

fn = sys.argv[1]
d = json.load(open(fn))
recs = d['results']; nrep = d['args']['nrep']
ms = sorted({r['m'] for r in recs}); Bs = sorted({r['B'] for r in recs})
get = {(r['B'], r['m']): r for r in recs}


def mult(r, mom):
    return np.mean([r[f'mult{i}'][mom] for i in range(nrep)])


for mom, ex, tk, fk in (('M6', 3, 'T6N3', 'full_M6'), ('M4', 2, 'T4N2', 'full_M4')):
    print(f'\n**{mom}** = sum_u |S_u|^{mom[1]} / (R N^{ex}): actual (multiplicative surrogate); standard error of actual in brackets\n')
    print('| B | R | ' + ' | '.join(f'm={m:.2f}' for m in ms) + ' |')
    print('|---:|---:|' + '---:|' * len(ms))
    for B in Bs:
        row = []
        for m in ms:
            r = get[(B, m)]
            se = r['actual']['se' + mom[1]]
            row.append(f"{r['actual'][mom]:.3f} ({mult(r, mom):.3f}) [{se:.3f}]")
        print(f'| {B} | {get[(B, ms[0])]["R"]} | ' + ' | '.join(row) + ' |')
    print('| N^%d/R at largest B | | ' % ex + ' | '.join(f"{get[(Bs[-1], m)]['N']**ex/get[(Bs[-1], m)]['R']:.1f}" for m in ms) + ' |')
    print('| N, #terms at largest B | | ' + ' | '.join(f"{get[(Bs[-1], m)]['N']:.0f}, {get[(Bs[-1], m)]['C']}" for m in ms) + ' |')
    print('| exact diagonal T/N^%d at largest B | | ' % ex + ' | '.join(f"{get[(Bs[-1], m)][tk]:.3f}" for m in ms) + ' |')
    print('| full Dirichlet family mod q~R, largest B | | ' + ' | '.join(f"{get[(Bs[-1], m)][fk]:.1f}" for m in ms) + ' |')
