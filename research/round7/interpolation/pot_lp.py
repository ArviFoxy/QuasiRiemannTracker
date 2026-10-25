r"""L -> infinity limit of the confluent (tight-cluster) model, as a logarithmic-potential LP.
(1/L) log|g(v)| = sum_m w_m log|v - zeta_m| + C - dc*v,   kappa = sum w_m = (#zeros)/L.
Minimize kappa subject to:  >= 0 at r1, r2;  <= -theta*c(v) on (r1,r2);  [bounded] <= 0 on [0,V]\(r1,r2).
Candidate zeros zeta: complex grid (heights h>0 avoid evaluation singularities).
"""
import numpy as np, sys
from scipy.optimize import linprog
from common import R1, R2, tent

def solve(theta=1.0, bounded=False, V=3.0, dc=0.0, xs=None, hs=(0.003, 0.01, 0.03, 0.08, 0.2), nev=600):
    if xs is None:
        xs = np.linspace(-0.5, V+0.5, 341) if bounded else np.linspace(R1-0.3, R2+0.3, 241)
    Z = np.array([x+1j*h for x in xs for h in hs])
    vin = np.linspace(R1, R2, nev+2)[1:-1]
    rows = []; rhs = []
    def P(v):  # matrix of log|v - zeta|
        return np.log(np.abs(np.asarray(v)[:, None] - Z[None, :]))
    # variables: w (len Z) >=0, C free
    Ain = P(vin); rows.append(np.hstack([Ain, np.ones((len(vin), 1))])); rhs.append(-theta*tent(vin) + dc*vin)
    Aend = P(np.array([R1, R2])); rows.append(np.hstack([-Aend, -np.ones((2, 1))])); rhs.append(-dc*np.array([R1, R2]))
    if bounded:
        vout = np.concatenate([np.linspace(0, R1, 300), np.linspace(R2, V, 600)])
        Ao = P(vout); rows.append(np.hstack([Ao, np.ones((len(vout), 1))])); rhs.append(dc*vout)
    A = np.vstack(rows); b = np.concatenate(rhs)
    c = np.concatenate([np.ones(len(Z)), [0.0]])
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)]*len(Z)+[(None, None)], method="highs")
    if res.status != 0:
        return None, None, None
    return res.fun, Z, res.x[:-1]

if __name__ == "__main__":
    for bounded in (False, True):
        for dc in ([0.0] if not bounded else [0.0, 0.01, 0.02, 0.04]):
            k, Z, w = solve(1.0, bounded, dc=dc)
            if k is None:
                print(f"bounded={bounded} dc={dc}: infeasible"); continue
            big = w > 1e-6*w.max()
            print(f"bounded={bounded!s:5} dc={dc:.3f}  kappa_min={k:.5f}   support Re in [{Z[big].real.min():.3f},{Z[big].real.max():.3f}]"
                  f"  mass in (r1,r2): {w[(Z.real>R1)&(Z.real<R2)].sum():.5f}", flush=True)
