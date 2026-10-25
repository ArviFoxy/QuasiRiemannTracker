r"""General free-coefficient model at finite L:
   g(v) = sum_j y_j exp(L*mu_j*v),  mu_j = rho_j - rho (Re mu_j <= 0), y_j complex free.
Constraints: g(r1)=1, Re(e^{-i phi} g(r2)) >= 1 (phi scanned),
             |g(v)| <= t*exp(-theta*c(v)*L) on (r1,r2)   (dip, minimize t),
             [bounded] |g(v)| <= B on [vlo,V] \ (r1,r2)   (pointwise bound from zero-free region).
|z|<=b imposed as Re(e^{-i th_m} z) <= b, m=0..M-1 (polygon; relaxes |z| by <= 1/cos(pi/M)).
"""
import numpy as np
from scipy.optimize import linprog
from common import R1, R2, tent

def build(mu, L, theta, bounded, V, B, vlo, M, nin, nout):
    th = np.linspace(0, np.pi, nin+2)[1:-1]
    vin = 0.5*(R1+R2) - 0.5*(R2-R1)*np.cos(th)
    E_in = np.exp(L*np.outer(vin, mu))                   # (nin,k)
    b_in = np.exp(-theta*tent(vin)*L)
    blocks = [(E_in/b_in[:, None], True)]
    if bounded:
        vout = np.concatenate([np.linspace(vlo, R1, nout//3), np.linspace(R2, V, nout - nout//3)])
        blocks.append((np.exp(L*np.outer(vout, mu))/B, False))
    return blocks

def solve(mu, L, theta=1.0, bounded=True, V=3.0, B=1.0, vlo=0.0, M=16, nin=300, nout=600, nphi=8):
    mu = np.asarray(mu, dtype=complex); k = len(mu)
    blocks = build(mu, L, theta, bounded, V, B, vlo, M, nin, nout)
    angs = 2*np.pi*np.arange(M)/M
    rows = []; rhs = []
    for (A, is_dip) in blocks:
        for a in angs:
            Z = np.exp(-1j*a)*A          # Re(Z @ y) with y = yr + i yi : Re(Z) yr - Im(Z) yi
            R = np.hstack([Z.real, -Z.imag])
            if is_dip:
                rows.append(np.hstack([R, -np.ones((R.shape[0], 1))])); rhs.append(np.zeros(R.shape[0]))
            else:
                rows.append(np.hstack([R, np.zeros((R.shape[0], 1))])); rhs.append(np.ones(R.shape[0]))
    A_ub0 = np.vstack(rows); b_ub0 = np.concatenate(rhs)
    e1 = np.exp(L*mu*R1); e2 = np.exp(L*mu*R2)
    A_eq = np.array([np.concatenate([e1.real, -e1.imag, [0]]), np.concatenate([e1.imag, e1.real, [0]])])
    b_eq = np.array([1.0, 0.0])
    best = (np.inf, None)
    for phi in 2*np.pi*np.arange(nphi)/nphi:
        z = np.exp(-1j*phi)*e2
        row = -np.concatenate([z.real, -z.imag, [0]])
        A_ub = np.vstack([A_ub0, row]); b_ub = np.concatenate([b_ub0, [-1.0]])
        c = np.zeros(2*k+1); c[-1] = 1
        res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(None, None)]*(2*k)+[(0, None)], method="highs")
        if res.status == 0 and res.x[-1] < best[0]:
            best = (res.x[-1], res.x[:k] + 1j*res.x[k:2*k])
    return best

def trig_config(k, omega, L, d=0.0):
    """k zeros on Re = a - d, heights spaced omega/L, centred at 0."""
    y = (np.arange(k) - (k-1)/2)*omega/L
    return -d + 1j*y

if __name__ == "__main__":
    import sys
    L = float(sys.argv[1]) if len(sys.argv) > 1 else 100
    for omega in [0.5, 1.0, 2.0, 4.0, 8.0]:
        for k in [4, 8, 12, 16, 24, 32, 48]:
            t, y = solve(trig_config(k, omega, L), L, bounded=True)
            tu, _ = solve(trig_config(k, omega, L), L, bounded=False)
            print(f"L={L:.0f} omega={omega:4.1f} k={k:3d}  t_bounded={t:9.3e}  t_unbounded={tu:9.3e}", flush=True)
