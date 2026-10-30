"""Exact (kernel-mirror) best N and a minimal window list for a full design.
args: Lend sMinus mMinus eleven h('-' = 7-digit ceiling floor) pCap N0"""
import sys, math
from fractions import Fraction as Fr
import mirror3 as M, cover3
from exact_run import windows
from model import hceiling
Lend, sM, mM, el = (Fr(a) for a in sys.argv[1:5]); hfix = None if sys.argv[5] == '-' else Fr(sys.argv[5])
pCap = Fr(sys.argv[6]); N0 = int(sys.argv[7])
pB = Fr(99999, 100000)
capL = Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - Lend)
consts = dict(mMinus=mM, sMinus=sM, eleven=el)
M.set_constants(**consts)
def K_of(N):
    c = Fr(N, 50000000); th = 1 - c
    h = hfix if hfix is not None else Fr(math.floor(hceiling(th) * 10 ** 7), 10 ** 7)
    return M.Const(c=c, h=h, reserve=Fr(1, 10 ** 8), cB=pB, cL=Lend, cCap=capL, pB=pB, pL=Lend, pCap=pCap, numCap=Fr(3, 40), dm=Fr(19, 25), w=Fr(1, 100))
plos = [Fr(0), Fr(1, 4), Fr(3, 8), Fr(7, 16), Fr(15, 32), Fr(31, 64), Fr(63, 128), Fr(127, 256), Fr(255, 512)]
ws = windows(cover3.Oracle(K_of(N0)), consts, ('C', 'capC', 'capP'), plos)
lo, hi = N0 - 1500, N0 + 1500
if not cover3.Oracle(K_of(lo)).run(ws)[0]:
    print('lo fails'); sys.exit()
while hi - lo > 1:
    mid = (lo + hi) // 2
    if cover3.Oracle(K_of(mid)).run(ws)[0]: lo = mid
    else: hi = mid
K = K_of(lo)
ok, res = cover3.Oracle(K).run(ws)
used = sorted(set(i for e in res for i in res[e]['used']))
small = [ws[i] for i in used]
changed = True
while changed:
    changed = False
    for i in range(len(small)):
        trial = small[:i] + small[i + 1:]
        if cover3.Oracle(K).run(trial)[0]:
            small = trial; changed = True; break
ok2, res2 = cover3.Oracle(K).run(small)
print('Lend %s sMinus %s mMinus %s eleven %s h %s pCap %s: best N %d theta = %.8f (c = %d/50000000), h = %s, cover %s, newTop %d leaves/%d tests' % (
    Lend, sM, mM, el, 'ceil' if hfix is None else hfix, pCap, lo, float(1 - Fr(lo, 50000000)), lo, K.h, ok2, res2['newTop']['leaves'], res2['newTop']['tests']))
for w in small: print('   window', w[0], w[1], w[2], w[3])
