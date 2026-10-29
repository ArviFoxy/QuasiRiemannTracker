"""Face gain of a doubled chain vs the base chain at equal L, against the return-side carrying cost Lam*X_k.
usage: python3 dB.py chain.json MODE PAR"""
import sys, json
import price as PR

base = PR.load('chains/base.json')
bmap = {round(r['L'], 4): r['B'] for r in base}
fn, mode, par = sys.argv[1], sys.argv[2], float(sys.argv[3])
rows = PR.load(fn)
X = PR.dvol(rows, mode, par)
print('%s: %d steps, end L=%.4f B=%.6f, X_end=%.3e' % (fn, len(rows), rows[-1]['L'], rows[-1]['B'], X[-1]))
for k in list(range(9, len(rows), 10)) + [len(rows) - 1]:
    r = rows[k]
    L = round(r['L'], 4)
    dB = r['B'] - bmap[L] if L in bmap else float('nan')
    print('  step %3d L=%.4f B=%.6f  dB_vs_base=%+.3e  Lam*X=%.3e  2Lam*X=%.3e  net(vol)=%+.3e' % (
        k, r['L'], r['B'], dB, r['L'] * X[k], 2 * r['L'] * X[k], dB - r['L'] * X[k]))
