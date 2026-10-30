"""Small tables for PRIMEROWS.md from the JSON outputs:
  shape  M6/M2^3 of the actual (prime rows P, the same rows artificially masked at pi_7 A, genuine pi_7 * pi' rows G) and of
         the surrogate without / with the mask, from primerows_artmask.py;
  dual   dual surrogate (random model on the dual representation) against the actual, per class and conductor stratum,
         pooled over c with the row weights of the run, from primerows_dualsurr.py.
usage: python3 -I primerows_tables.py
"""
import sys, os, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
L = os.path.join(HERE, 'logsP')

print('shape table: normalised sixth moment M6/M2^3 (actual: P prime rows, A same rows masked at pi_7, G genuine pi_7*pi\'; surrogate: no mask / mask pi_7)')
print('| B | m | P | A | G | sur, no mask | sur, mask 7 | A/P (actual) | mask/no mask (surrogate) | ratio P/sur | ratio A/sur7 | ratio G/sur7 |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|')
for B in ('1e5', '3e5'):
    f = os.path.join(L, f'artmask_{B}_q7.json')
    if not os.path.exists(f):
        continue
    for r in json.load(open(f))['results']:
        P = r['P'] / r['M2P'] ** 3; A = r['A'] / r['M2A'] ** 3; G = r['G'] / r['M2G'] ** 3
        s0 = r['sur0'] / r['sur0M2'] ** 3; sq = r['surq'] / r['surqM2'] ** 3
        print(f"| {B} | {r['m']:.2f} | {P:.2f} | {A:.2f} | {G:.2f} | {s0:.2f} | {sq:.2f} | {A/P:.3f} | {sq/s0:.3f} | {r['P']/r['sur0']:.3f} | {r['A']/r['surq']:.3f} | {r['G']/r['surq']:.3f} |")

print('\ndual table: M6 of the random model applied to the dual sum (dsur, row sample) vs the actual (all rows of the stratum)')
print('| B | m | class | c=0 dsur / act | c=1 dsur / act | c=2 dsur / act | pooled dsur | pooled actual | pooled osur | dsur/osur | act/osur |')
print('|---|---|---|---|---|---|---|---|---|---|---|')
for B in ('1e5', '3e4'):
    f = os.path.join(L, f'dualsurr_{B}.json')
    if not os.path.exists(f):
        continue
    R = json.load(open(f))['results']
    for m in sorted({r['m'] for r in R}):
        for cls in ('prime', 'comp7', 'compother'):
            rs = {r['c']: r for r in R if r['m'] == m and r['cls'] == cls}
            if len(rs) < 3:
                continue
            n = np.array([rs[c]['n_all'] for c in (0, 1, 2)], float)
            ds = np.array([rs[c]['dM6'] for c in (0, 1, 2)]); ac = np.array([rs[c]['aM6_all'] for c in (0, 1, 2)])
            os_ = np.array([rs[c]['oM6_all'] for c in (0, 1, 2)])
            w = n / n.sum()
            cells = ' | '.join(f'{ds[i]:.2f} / {ac[i]:.2f}' for i in range(3))
            print(f'| {B} | {m:.2f} | {cls} | {cells} | {w @ ds:.2f} | {w @ ac:.2f} | {w @ os_:.2f} | {(w @ ds)/(w @ os_):.3f} | {(w @ ac)/(w @ os_):.3f} |')
