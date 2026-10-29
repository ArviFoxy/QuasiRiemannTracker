import ode2
c0 = ode2.Chain2(gain=0.0, dfac=1.0, boot=True)
c1 = ode2.Chain2(gain=1.0, dfac=1.0, boot=True)
print('| L | q (marked) | B unmarked | B marked | dB | s0 unmarked | s0 marked | s0 ratio | gain at (q, s0) |')
print('|---|---|---|---|---|---|---|---|---|')
import gainc as G
for L in (2.55, 2.50, 2.40, 2.30, 2.25, 2.20, 2.10, 2.00, 1.95, 1.93):
    if L < c1.Lmin: continue
    B0, B1 = c0.B(L), c1.B(L)
    s0, s1 = c0.slope(L), c1.slope(L)
    q = c1.qinf(L)
    g = float(G.gainK(q, 8, B1, L, 0.1, s1, 1.0))
    print('| %.2f | %.4f | %.5f | %.5f | %+.5f | %.4f | %.4f | %.3f | %.4f |' % (L, q, B0, B1, B1 - B0, s0, s1, s1 / s0, g))
