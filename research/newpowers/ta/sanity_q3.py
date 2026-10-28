"""Q3 sanity: reproduce PR 86's chain and theta = 0.8739558 with the marked gain switched off.
  (a) exact return, PR 86 constants/box/branches/windows, PR 86's own step-46 face (Lean rationals)  -> least theta
  (b) float replica of the PR 86 chain (gain = 0, floor 13/20, dfac 0.999, boot face 0.99999, 2.5715, 0.1397) vs the Lean chain
  (c) the exact return on the replica's step-46 face; role split (46/38) on PR 86's faces
"""
import sys, os, json, time
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'tc'))
sys.path.insert(0, HERE)
import pr86, best
import chain2 as C2
import exact


def theta_fixed_h(cfg, h, lo=8739000000, hi=8740200000, unit=10**10):
    """least theta (units 1e-10) passing at fixed h by bisection"""
    ok = lambda t: pr86.certifiable(cfg.copy(th=Fr(t, unit), h=h))
    assert ok(hi) and not ok(lo)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi / unit


cfg0 = pr86.Cfg()
print('(a) PR 86 declared theta 0.8739558 certifiable with its own constants:', pr86.certifiable(cfg0, why=True))
t = theta_fixed_h(cfg0, Fr(8051, 10000))
print('    least theta at h = 8051/10000, PR 86 face (step 46), PR 86 box, windows Collet, branches old/C/Pcap: %.10f' % t)
print('    7-digit (1e-7 grid):', pr86.theta_star(cfg0))
cf = best.theta_best(cfg0, anchor=8739570, unit=10**7)
print('    floor-coupled h (largest allowed by floor_margin):', cf[0] / 1e7, float(cf[1]))
r = exact.theta_exact(float(cfg0.BC), float(cfg0.LC), float(cfg0.BP), float(cfg0.LP), guess=0.873956, windows='collet',
                      branches=['old', 'C', 'Pcap'], ell_max=Fr(171, 1000))
print('    single face, box ell<0.171, collet, old/C/Pcap, floor-coupled h, 1e-9:', r)
r = exact.theta_exact(float(cfg0.BC), float(cfg0.LC), float(cfg0.BP), float(cfg0.LP), guess=0.873956, windows='collet',
                      branches=exact.SIX, ell_max=Fr(18, 100))
print('    same, six branches, ell < 0.18:', r)

# role split on PR 86's own faces (steps 46 / 38)
lean = json.load(open(os.path.join(HERE, 'tc', 'chain86.json')))
f46, f38 = lean[46], lean[38]
C = (float(Fr(f46['B'])), float(Fr(f46['L']))); P = (float(Fr(f38['B'])), float(Fr(f38['L'])))
r = exact.theta_exact(C[0], C[1], P[0], P[1], guess=0.873955, windows='collet', branches=['old', 'C', 'Pcap'], ell_max=Fr(171, 1000))
print('    role split 46/38 on PR 86 faces (old/C/Pcap, ell<0.171):', r)
r = exact.theta_exact(C[0], C[1], P[0], P[1], guess=0.873955, windows='collet', branches=exact.SIX, ell_max=Fr(18, 100))
print('    role split 46/38, six branches, ell < 0.18:', r)

# (b) replica chain vs Lean
cfg = C2.Cfg(gain=0.0, floor=0.65)
rows = C2.run(cfg, Lend=2.3415, verbose=False)
print('(b) replica chain, gain 0, floor 0.65: %d steps; step 46: L=%.4f B=%.7f (Lean 0.9888151, diff %+.2e), s0=%.5f (Lean 0.06510)' % (
    len(rows), rows[45]['L'], rows[45]['B'], rows[45]['B'] - 0.9888151, rows[45]['s0']))
mx = max(abs(rows[k - 1]['B'] - float(Fr(lean[k]['B']))) for k in range(1, 47))
print('    max |B_replica - B_Lean| over the 46 steps: %.2e;  max |s0 diff| %.2e' % (
    mx, max(abs(rows[k - 1]['s0'] - float(Fr(lean[k]['s0']))) for k in range(1, 47))))
print('    binding gate at every step:', sorted(set(r['bind'] for r in rows)))
Cr = (rows[45]['B'], rows[45]['L']); Pr = (rows[37]['B'], rows[37]['L'])
r1 = exact.theta_exact(Cr[0], Cr[1], Cr[0], Cr[1], guess=0.873956, windows='collet', branches=['old', 'C', 'Pcap'], ell_max=Fr(171, 1000))
print('(c) replica faces: single face 46, PR 86 return (old/C/Pcap, ell<0.171, floor-coupled h):', r1)
r2 = exact.theta_exact(Cr[0], Cr[1], Pr[0], Pr[1], guess=0.873955, windows='collet', branches=['old', 'C', 'Pcap'], ell_max=Fr(171, 1000))
print('    replica faces role split 46/38 (PR 86 return):', r2)
