"""Exact cover with h overridden (floor margin relaxed; h capped by the transport box h < 806/1000)."""
import sys
from fractions import Fraction as Fr
import mirror3 as M, cover3
from exact_run import windows
Lend = Fr(sys.argv[1]); hfix = Fr(sys.argv[2]); numCap = Fr(sys.argv[3]) if len(sys.argv) > 3 else Fr(3, 40)
capL = Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - Lend)
M.set_constants(mMinus=Fr(3, 10), sMinus=Fr(1, 10000), eleven=Fr(1, 2))
consts = dict(mMinus=Fr(3, 10), sMinus=Fr(1, 10000), eleven=Fr(1, 2))
des = dict(cB=Fr(99999, 100000), cL=Lend, cCap=capL, w=Fr(1, 100), pB=Fr(99999, 100000), pL=Lend, pCap=Fr(12, 100), numCap=numCap)
def K_of(N):
    c = Fr(N, 50000000)
    return M.Const(c=c, h=hfix, reserve=Fr(1, 10 ** 8), cB=des['cB'], cL=des['cL'], cCap=des['cCap'], pB=des['pB'], pL=des['pL'], pCap=des['pCap'], numCap=des['numCap'], dm=Fr(19, 25), w=des['w'])
plos = [Fr(0), Fr(1, 4), Fr(3, 8), Fr(7, 16), Fr(15, 32), Fr(31, 64), Fr(63, 128), Fr(127, 256), Fr(255, 512)]
N0 = int(sys.argv[4]) if len(sys.argv) > 4 else 6330000
O = cover3.Oracle(K_of(N0))
ws = windows(O, consts, ('C', 'capC', 'capP'), plos)
lo, hi = N0 - 3000, N0 + 3000
assert cover3.Oracle(K_of(lo)).run(ws)[0], 'lo fails'
while hi - lo > 1:
    mid = (lo + hi) // 2
    if cover3.Oracle(K_of(mid)).run(ws)[0]: lo = mid
    else: hi = mid
print('Lend', Lend, 'h', hfix, 'numCap', numCap, 'best N', lo, 'theta = %.8f' % float(1 - Fr(lo, 50000000)))
