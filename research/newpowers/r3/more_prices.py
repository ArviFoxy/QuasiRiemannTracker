"""Further prices (PM): face-level equivalents, plain-line shift, superposition test, partial-credit pairs."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pm import *

def theta(s, **kw):
    return scenario(s, **kw).theta_star()

print('== face-level equivalents of the same need')
for s in 'AB':
    m0 = scenario(s); fc = (m0.BC, m0.LC); fp = (m0.BP, m0.LP)
    t0 = m0.theta_star()
    # count face: B_C up / Lam_C down
    nB = needed(s, 'BC', fc[0], fc[0] + 0.02)
    nL = needed(s, 'LC', fc[1] - 0.2, fc[1])
    pB = needed(s, 'BP', fp[0], fp[0] + 0.02, sPnum=0.09)
    pL = needed(s, 'LP', fp[1] - 0.2, fp[1], sPnum=0.09)
    print(' %s: count face B_C %.7f -> %.7f (+%.2e) ; Lam_C %.5f -> %.5f (%.2f%%) ; physical face B_P +%.2e ; Lam_P %.5f -> %.5f (%.2f%%)' %
          (s, fc[0], nB, nB - fc[0], fc[1], nL, 100*(nL/fc[1]-1), pB - fp[0], fp[1], pL, 100*(pL/fp[1]-1)))
    print('    NB: priced with the numerator cap raised to 0.09 (PhysicalSchedule.cap_lt_fifth allows < 1/5); with 3/50 the clip s_P*d saturates after +5e-4 in B_P')

print('\n== plain line constant shift sPl (count exponent of the P line lowered by sPl at fixed m): needed')
for s in 'AB':
    v = needed(s, 'sPl', 0, 5e-3)
    d = float(scenario(s).binding()['delta'])
    print(' %s: sPl = %.3e  <=> extra plain slot width dz = sPl/(2 delta p) = %.3e  = %.2f%% of z_P(m*)=%.4f' % (s, v, v/(2*d*0.5), 100*v/(2*d*0.5)/0.0867, 0.0867))

print('\n== superposition (linearity) test for pairs at half size each (scenario A)')
cI_need, kL_need = 1.9941386, 0.83131557
eps_need, eE_need, wL_need = 0.0045901181, 1.6618599e-4, 8.6547105e-4
t0 = theta('A')
def shift(**kw): return theta('A', **kw) - t0
pairs = [('cI/2 + kL/2', dict(cI=2-(2-cI_need)/2, kL=5/6-(5/6-kL_need)/2)),
         ('cI/2 + eps/2', dict(cI=2-(2-cI_need)/2, eps_half=eps_need/2)),
         ('eE/2 + kL/2', dict(eE=eE_need/2, kL=5/6-(5/6-kL_need)/2)),
         ('eE/2 + cI/2', dict(eE=eE_need/2, cI=2-(2-cI_need)/2)),
         ('eE/3+cI/3+kL/3', dict(eE=eE_need/3, cI=2-(2-cI_need)/3, kL=5/6-(5/6-kL_need)/3)),
         ('wL/2 + eps/2', dict(wL=wL_need/2, eps_half=eps_need/2))]
for nm, kw in pairs:
    s = shift(**kw)
    print('  %-18s shift %+.4e  (target %+.4e)  gap to bar %+.2e' % (nm, s, BAR - t0, theta('A', **kw) - BAR))

print('\n== relative sizes of the needed improvements (A | B)')
print('  c_I: 2 -> 1.99414 (-0.293%%) | 1.98956 (-0.522%%)')
print('  k_L: 5/6 -> 0.83132 (-0.24%%) | 0.82969 (-0.44%%)')
print('  eps/(1/2): +0.92%% | +1.67%% ; capacity +0.92%% | +1.66%%')
