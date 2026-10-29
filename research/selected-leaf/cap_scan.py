"""E5. Value of count faces (0.99999, L, cap) from the selected-leaf native line, physical face at the line's end
(L_end).  The cap gate allows fast cap growth when the selected fraction a is not minimal, so caps up to
refPos (≈ 0.16) are reachable; scan which (L, cap) clears the bar.  [numerical, global check]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'face-region', 'value'))
from globalcheck import theta_global
B = 0.99999
for Lend in (2.02, 2.05):
    PF = (B, Lend)
    for L in (2.4, 2.3, 2.2, 2.1, 2.05):
        if L < Lend: continue
        for cap in (0.1, 0.12, 0.14):
            t, where = theta_global((B, L, cap), PF)
            print('phys L=%.2f  count (%.5f, %.3f, cap %.3f): theta* = %.8f  %+.3e  %s' % (Lend, B, L, cap, t, t - 0.87387234, where), flush=True)
