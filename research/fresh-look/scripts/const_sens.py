"""Exact sensitivity of theta to the row constants of the return (13/75, 9/100, 3/4).

Patches mirror3.EbaseQ / rowQ with parametrised constants and bisects the best N with the kernel mirror,
at the selected-leaf configuration (Lend 401/200, sMinus 27/1000, mMinus 3/10, h 8001361/10^7, pCap 3/25).
usage: python3 const_sens.py THIRTEEN NINE THREE4   (fractions; e.g. 13/75 9/100 3/4)"""
import sys
from fractions import Fraction as Fr
import mirror3 as M, cover3
from exact_run import windows

T13, N9, W34 = (Fr(a) for a in sys.argv[1:4])
X, Y = M.X, M.Y


def EbaseQ(K, d, cap):
    return M.add(M.C(Fr(1, 2) + T13 * K.h - K.y / 2 - K.ell / 2 - N9 * d),
                 M.add(M.smul(Fr(1, 2), X), M.smul(K.ell - cap / 2, M.mul(X, Y))))


def rowQ(K, d, cap, J, N):
    return M.sub(M.mul(J, M.sub(M.C(K.theta - K.reserve), EbaseQ(K, d, cap))), M.smul(W34 * d, N))


M.EbaseQ, M.rowQ = EbaseQ, rowQ
Lend = Fr(401, 200)
pB = Fr(99999, 100000)
capL = Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - Lend)
consts = dict(mMinus=Fr(3, 10), sMinus=Fr(27, 1000), eleven=Fr(11, 25))
M.set_constants(**consts)


def K_of(N):
    return M.Const(c=Fr(N, 50000000), h=Fr(8001361, 10 ** 7), reserve=Fr(1, 10 ** 8), cB=pB, cL=Lend, cCap=capL,
                   pB=pB, pL=Lend, pCap=Fr(3, 25), numCap=Fr(3, 40), dm=Fr(19, 25), w=Fr(1, 100))


plos = [Fr(0), Fr(1, 4), Fr(3, 8), Fr(7, 16), Fr(15, 32), Fr(31, 64), Fr(63, 128), Fr(127, 256), Fr(255, 512)]
N0 = 6329401
ws = windows(cover3.Oracle(K_of(N0)), consts, ('C', 'capC', 'capP'), plos)
lo, hi = N0 - 3000, N0 + 3000
if not cover3.Oracle(K_of(lo)).run(ws)[0]:
    print('lo fails'); sys.exit()
while hi - lo > 1:
    mid = (lo + hi) // 2
    if cover3.Oracle(K_of(mid)).run(ws)[0]: lo = mid
    else: hi = mid
print('13/75->%s 9/100->%s 3/4->%s: best N %d theta = %.8f (dtheta %+.3e vs 0.87341198)' % (
    T13, N9, W34, lo, float(1 - Fr(lo, 50000000)), float(1 - Fr(lo, 50000000)) - 0.87341198))
