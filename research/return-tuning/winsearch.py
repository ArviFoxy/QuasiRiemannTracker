"""Search for a small set of windows (maximal rectangles) that the kernel check accepts, using the exact mirror."""
import sys, time
from fractions import Fraction as Fr
import mirror as M
from windows import parse_windows

K = M.Const()

# 1. the 31 existing windows pass at depth 0 (as the Lean Compat module found)
t = time.time()
M.STATS['bern'] = 0
ok = all(M.windowCheck(K.toQ(w['branch']), 0, w['dlo'], w['dhi'], w['plo']) for w in parse_windows())
print('existing 31 windows pass at depth 0:', ok, f'({M.STATS["bern"]} Bernstein tests, {time.time() - t:.1f}s)')


def check(b, dlo, dhi, plo, k=6):
    M.STATS['bern'] = 0
    r = M.windowCheck(K.toQ(b), k, Fr(dlo), Fr(dhi), Fr(plo))
    return r, M.STATS['bern']


# 2. candidate large windows
cands = {
    'capP': [(Fr(9, 32), Fr(27, 64), Fr(3, 8)), (Fr(1, 4), Fr(7, 16), Fr(1, 4)), (Fr(9, 32), Fr(9, 16), Fr(3, 8)),
             (Fr(69, 128), Fr(141, 256), Fr(31, 64)), (Fr(1, 2), Fr(9, 16), Fr(15, 32))],
    'capC': [(Fr(21, 64), Fr(51, 128), Fr(7, 16)), (Fr(5, 16), Fr(25, 64), Fr(3, 8)), (Fr(21, 64), Fr(25, 64), Fr(13, 32))],
    'weakC7': [(Fr(51, 128), Fr(27, 64), Fr(7, 16)), (Fr(51, 128), Fr(7, 16), Fr(3, 8)), (Fr(25, 64), Fr(15, 32), Fr(3, 8))],
    'C': [(Fr(27, 64), Fr(69, 128), Fr(3, 8)), (Fr(13, 32), Fr(35, 64), Fr(3, 8)), (Fr(27, 64), Fr(35, 64), Fr(1, 4)),
          (Fr(27, 64), Fr(17, 32), Fr(0))],
}
for b, ws in cands.items():
    for (lo, hi, pl) in ws:
        t = time.time()
        r, n = check(b, lo, hi, pl)
        print(f'{b:7s} [{lo}, {hi}] x [{pl}, 1/2] ({float(lo):.4f}-{float(hi):.4f}, p>={float(pl):.4f}): {r}  '
              f'({n} tests, {time.time() - t:.1f}s)')
