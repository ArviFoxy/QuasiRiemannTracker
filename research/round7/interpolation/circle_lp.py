r"""Bounded trig model in the L -> infinity limit.
Zeros of L on Re s = a at heights spaced omega/L  =>  profile g(v) = q(exp(i*omega*v)), q a polynomial of
degree kappa*L.  If omega*V >= 2*pi the pointwise bound |g| <= 1 on [0,V] covers the whole unit circle.
(1/L) log|q(e^{i th})| = kappa * int log|e^{i th} - zeta| dnu(zeta) + C,  nu a probability measure on C.
Minimize kappa:  f <= 0 on the circle, f <= -c(th/omega) on the tent arc, f >= 0 at th1=omega*r1, th2=omega*r2.
"""
import numpy as np
from scipy.optimize import linprog
from common import R1, R2, tent

def solve(omega, theta=1.0, nth=720, radii=(0.6, 0.8, 0.9, 0.95, 0.98, 1.0, 1.02, 1.05, 1.1, 1.25, 1.6), nang=360,
          bounded=True):
    phis = 2*np.pi*(np.arange(nang)+0.5)/nang
    Z = np.array([r*np.exp(1j*p) for r in radii for p in phis])
    ths = 2*np.pi*(np.arange(nth)+0.13)/nth
    def Pm(th):
        return np.log(np.abs(np.exp(1j*np.asarray(th))[:, None] - Z[None, :]))
    th1, th2 = omega*R1, omega*R2
    assert th2 - th1 < 2*np.pi
    # tent values at circle points inside the arc (th1, th2), measured mod 2pi from th1
    rel = np.mod(ths - th1, 2*np.pi)
    inarc = (rel > 0) & (rel < th2 - th1)
    v = R1 + rel/omega
    cvals = np.where(inarc, theta*tent(v), 0.0)
    rows = []; rhs = []
    sel = inarc | bounded
    A = Pm(ths[sel]); rows.append(np.hstack([A, np.ones((A.shape[0], 1))])); rhs.append(-cvals[sel])
    Ae = Pm([th1, th2]); rows.append(np.hstack([-Ae, -np.ones((2, 1))])); rhs.append(np.zeros(2))
    res = linprog(np.concatenate([np.ones(len(Z)), [0]]), A_ub=np.vstack(rows), b_ub=np.concatenate(rhs),
                  bounds=[(0, None)]*len(Z)+[(None, None)], method="highs")
    if res.status != 0:
        return None, None, None
    return res.fun, Z, res.x[:-1]

if __name__ == "__main__":
    for omega in [0.5, 1, 2, 3, 4, 6, 2*np.pi, 8, 10, 12, 14]:
        if omega*(R2-R1) >= 2*np.pi: continue
        kb, Z, w = solve(omega, bounded=True)
        ku, _, _ = solve(omega, bounded=False)
        msg = ""
        if kb is not None:
            on = np.abs(np.abs(Z)-1) < 1e-9
            msg = f"mass on |z|=1: {w[on].sum():.4f}, inside: {w[np.abs(Z)<1-1e-9].sum():.4f}, outside: {w[np.abs(Z)>1+1e-9].sum():.4f}"
        print(f"omega={omega:6.3f}  kappa_bounded={kb if kb is None else round(kb,5)}  kappa_unbounded={ku if ku is None else round(ku,5)}  {msg}", flush=True)
