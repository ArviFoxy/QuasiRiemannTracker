"""Corner (r*, m*, t*) from the Lean/NR2 formulas; test the near-identity r* = 3m* - 1/2."""
import json
from fractions import Fraction as Fr
def corner(delta, p, B, Lam):
    w = 1/Lam
    V = 5/6 - delta; D = 3 - p - 4*p*w; A = 2 - 4*p*w; C0 = 1 - 2*p*B*w; U = (1-p)*C0
    J = V*D + delta*(1-p)*A; N = (1-delta)*J + V*delta*U; T = J + delta*U
    Rn = A*T + (2*p*B*w - p)*J; Mn = D*T - Rn
    return N/J, T/J, Rn/(D*J), Mn/(D*J)
nodes = json.load(open('/home/user/QuasiRiemannTracker/research/repeated-marks/cchain_k8b.json'))
faces = {i: (float(Fr(nodes[i]['B'])), float(Fr(nodes[i]['L']))) for i in (52, 58)}
faces['PR69_P'] = (0.96739031091242, 3.27307995389766); faces['PR69_C'] = (0.96226151753982, 3.14813176381578)
for name, (B, Lam) in faces.items():
    for delta in (0.4546, 0.455):
        R, t, r, m = corner(delta, 0.5, B, Lam)
        print(f"face {name}: B={B:.5f} Lam={Lam:.5f} delta={delta}: R={R:.6f} t*={t:.5f} r*={r:.5f} m*={m:.5f}"
              f"  r*+m*-t*={r+m-t:.1e}  3m*-1/2-r*={3*m-0.5-r:+.5f}  2m*-r*={2*m-r:.4f}  t*-1={t-1:.4f}")
