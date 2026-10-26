"""Numbers for REPORT.md section 2: the binding branch at the design face, the triple point, and the
closed-form HIGH floor q_min; plus the full-gate margins of every branch/gate at the design node."""
import sys, os, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'faceless-chain'))
sys.path.insert(0, os.path.join(HERE, '..', 'mixed-step'))
sys.argv = ['x', '/dev/null', '6']
import continuum_mixed as CM
G = CM.G
import closed_form as CF

rows = json.load(open(os.path.join(HERE, 'flows', 'orig.json')))
r = [x for x in rows if abs(x['s'] - 0.057) < 1e-9][0]
s, E, L, q = r['s'], r['E'], r['L'], r['q']
B = E + L*s; T = E + s
print(f"design face s={s} E={E:.6f} B={B:.6f} L={L:.5f} q={q:.5f}  T=E+s={T:.6f}")
# branch-5 root at nu = q, p = 1/2 (a ~ 0, F = 1)
nu = q; w = 5 - 6*nu
xi = (5 + w*(1 + B/(2*(L - 1))))/(6*nu + w*(2 + L/(2*(L - 1))))
I = 2*xi - 1; P = (L*xi - B)/(L - 1); tcut = I + P/2; tmax = (5 - 6*nu*xi)/w
print(f"branch-5 root xi={xi:.6f} (T={T:.6f}, xi-T={xi-T:.2e});  I=2xi-1={I:.5f}, P={P:.5f} (E={E:.5f}), "
      f"t_cut=I+P/2={tcut:.5f}, plain capacity (B-P)/L={(B-P)/L:.5f} (s={s})")
# branch 3 (plain slot-limited) root, S = s
xi3 = (5 + w*(1 + s/2))/(6*nu + 2.5*w)
print(f"branch-3 root xi3={xi3:.6f}  (branch 3 and 5 tie at the crossing: {xi3-xi:.2e})")
# closed-form floor
print(f"q_min(closed form, mh=0) = {CF.q_min(E, s, L, mh=0.0):.5f}; formula 5(5E+4s-4)/(6(3E+2s-2)) = "
      f"{5*(5*E + 4*s - 4)/(6*(3*E + 2*s - 2)):.5f};  flow q = {q:.5f}")
print(f"LOW pin: q_max = L/(6B-L) = {L/(6*B - L):.5f};  slope law 6qE/(1+q-6qs) = {6*q*E/(1 + q - 6*q*s):.5f} (flow L={L:.5f})")
# full-gate margins at the node
n = G.node(B, L, 0.075, q, G.FINE)
for b in (s, 0.075):
    m = G.margins(n, n, n, b)
    nuv = np.linspace(q, 0.75, 41); pv = np.linspace(0, 0.5, 101)
    hg = G.high_gate(n, n, n, b, nuv, pv)
    mins = [hg[k].min() for k in range(6)]
    print(f"b={b}: scalar {m['scalar']:.2e} sector {m['sector']:.4f} high {m['high']:.2e}; per-branch mins "
          + ' '.join(f'{x:.2e}' for x in mins))
# sensitivities of q_min
for name, kw in [('kL', dict(kL=5/6 - 1e-4)), ('cI', dict(cI=2 - 1e-4))]:
    d = (CF.q_min(E, s, L, mh=0.0, **kw) - CF.q_min(E, s, L, mh=0.0))/(-1e-4)
    print(f"d q_min / d {name} = {d:.4f}")
