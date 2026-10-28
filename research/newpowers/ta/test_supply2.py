import sys
sys.path.insert(0, '$SCRATCH/analysis/B2')
import numpy as np, counts as C, supply as S
import markedcount as M
k = 0.74791
print('compare nested-bisection (full-width-only) with B2 brute force markedcount.count_exponent')
for nu in (0.6, 0.65):
    for x in (0.0, 0.2, 0.5):
        for sg in (7/37, 0.12, 0.09, 0.07, 0.05):
            b2 = M.count_exponent(nu, x, k, sg, N=801)[0]
            me = S.R_supply(nu, x, k, sg, False)[0]
            mp = S.R_supply(nu, x, k, sg, True)[0]
            print('nu=%.2f x=%.1f sigma=%.4f  B2 brute=%.5f  mine(full)=%.5f  diff=%+.1e   partial-z=%.5f   rowCount=%.5f' % (nu, x, sg, b2, me, me-b2, mp, C.rowCount(nu, x, k)))
