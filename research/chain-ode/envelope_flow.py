"""Integrate the switching flow E' = -6qE/(1-6qs), 6q = max_p 6q_p(s,E), with the closed-form class
thresholds 6q_p = 5((3-p)E + 4ps - 2)/((1+p)E + 4p^2 s - 2p), p in [0, 1/2], capped by the natural
face slope K = 4.4973108; compare with the continuum ceiling envelope (variational-ceiling).
Run: python3 envelope_flow.py"""
import numpy as np
K = 4.4973108
P = np.linspace(0.0, 0.5, 501)
def six_q(s, E):
    v = 5*((3-P)*E + 4*P*s - 2)/((1+P)*E + 4*P**2*s - 2*P)
    i = np.argmax(v); return v[i], P[i]
def run(ds=1e-6, s_end=0.0455):
    s, E = 0.0, 1.0; rec = {}
    marks = [0.0135, 0.02, 0.03, 0.0412, 0.045]
    while s < s_end:
        q6, pstar = six_q(s, E)
        slope = min(q6*E/(1 - q6*s), K)
        for m in marks:
            if m not in rec and s >= m: rec[m] = (E, slope, pstar, q6/6)
        E -= slope*ds; s += ds
    return rec
rec = run()
ref = {0.0412: 0.8371458, 0.045: 0.8262527}
for m, (E, sl, ps, q) in sorted(rec.items()):
    extra = f"  ceiling E={ref[m]:.7f}  diff={E-ref[m]:+.2e}" if m in ref else ""
    print(f"s={m:.4f}  E={E:.7f}  slope={sl:.4f}  p*={ps:.3f}  q={q:.4f}{extra}")
