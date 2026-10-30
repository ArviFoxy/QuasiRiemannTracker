"""Exact cover, bisection on N, h = 7-digit floor of the floor-margin ceiling (or a fixed h)."""
import sys, math
from fractions import Fraction as Fr
import mirror3 as M, cover3
from exact_run import windows
from model import hceiling
Lend = Fr(sys.argv[1]); N0 = int(sys.argv[2]); hfix = Fr(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else None
pB = Fr(99999, 100000)
capL = Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - Lend)
consts = dict(mMinus=Fr(3, 10), sMinus=Fr(1, 10000), eleven=Fr(1, 2))
M.set_constants(**consts)
def K_of(N):
    c = Fr(N, 50000000); th = 1 - c
    h = hfix if hfix is not None else Fr(math.floor(hceiling(th) * 10 ** 7), 10 ** 7)
    return M.Const(c=c, h=h, reserve=Fr(1, 10 ** 8), cB=pB, cL=Lend, cCap=capL, pB=pB, pL=Lend, pCap=Fr(12, 100), numCap=Fr(3, 40), dm=Fr(19, 25), w=Fr(1, 100))
plos = [Fr(0), Fr(1, 4), Fr(3, 8), Fr(7, 16), Fr(15, 32), Fr(31, 64), Fr(63, 128), Fr(127, 256), Fr(255, 512)]
ws = windows(cover3.Oracle(K_of(N0)), consts, ('C', 'capC', 'capP'), plos)
lo, hi = N0 - 2000, N0 + 2000
assert cover3.Oracle(K_of(lo)).run(ws)[0], 'lo fails'
assert not cover3.Oracle(K_of(hi)).run(ws)[0], 'hi passes'
while hi - lo > 1:
    mid = (lo + hi) // 2
    if cover3.Oracle(K_of(mid)).run(ws)[0]: lo = mid
    else: hi = mid
print('Lend', Lend, 'h', 'ceiling' if hfix is None else hfix, 'best N', lo, 'theta = %.8f' % float(1 - Fr(lo, 50000000)))
