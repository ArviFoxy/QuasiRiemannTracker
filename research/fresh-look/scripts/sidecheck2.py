"""gen_return86 side conditions (box, schedule, natural join, sources) for the proposed configurations,
with the floor-margin constant as a parameter mu (1/200 in the merged transport)."""
import sys
sys.path.insert(0, '../retune')
from fractions import Fraction as Fr
from types import SimpleNamespace as NS
import gen_return86 as G
def config(N, h, L, cap, pCap, sMinus, mMinus, mu=Fr(1, 200)):
    th = 1 - Fr(N, 50000000); c = 1 - th
    ell = 4 * c - Fr(1, 3); x = 1 + ell - h; y = h - 2 * ell
    B = Fr(99999, 100000)
    P = NS(theta=th, h=h, ell=ell, x=x, y=y, kappa=1 - 2 * c, dp=h + Fr(1, 10 ** 10), numCap=Fr(3, 40), dm=Fr(19, 25),
           pL=L, pB=B, K=Fr(9, 2), naturalM=(1 - Fr(9, 2) * sMinus) / 2, cCap=cap, pCap=pCap, cL=L, cB=B, mMinus=mMinus,
           reserve=Fr(1, 10 ** 8), srcC=(B, L, cap), srcP=(B, L, cap))
    r = G.side_conditions(P, 'arvi')
    signal = x / 2 + (y - x) / 12
    r['box.floor_margin (>=0)'] = signal - mu - (Fr(4, 25) * x - Fr(3, 20) - Fr(51, 100) * y + Fr(67, 100) * P.dp - Fr(3, 20) * ell)
    bad = {k: float(v) for k, v in r.items() if (v < 0 if '(>=0)' in k else v <= 0)}
    tight = sorted((float(v), k) for k, v in r.items())[:4]
    return bad, tight
capf = lambda L: Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - L)
for label, args in [
    ('1: L=101/50, h ceil', (6328381, Fr(800327, 1000000), Fr(101, 50), capf(Fr(101, 50)), Fr(3, 25), Fr(27, 1000), Fr(3, 10))),
    ('2: L=401/200, h ceil', (6329401, Fr(8001361, 10 ** 7), Fr(401, 200), capf(Fr(401, 200)), Fr(3, 25), Fr(27, 1000), Fr(3, 10))),
    ('3: L=401/200, h=0.8059999, mu=1/1000', (6330351, Fr(8059999, 10 ** 7), Fr(401, 200), capf(Fr(401, 200)), Fr(3, 25), Fr(27, 1000), Fr(3, 10), Fr(1, 1000))),
    ('3 with mu=1/200 (merged transport)', (6330351, Fr(8059999, 10 ** 7), Fr(401, 200), capf(Fr(401, 200)), Fr(3, 25), Fr(27, 1000), Fr(3, 10), Fr(1, 200))),
]:
    bad, tight = config(*args)
    print('%-40s failing: %s' % (label, bad if bad else 'none'))
    print('      tightest:', [(round(v, 7), k) for v, k in tight])
