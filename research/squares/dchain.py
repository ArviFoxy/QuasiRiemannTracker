"""Doubled-slot variants of the floor-1/2 marked density chain (T-A replica `ta/chain2.py`, K = 8 Lean gain),
with R2's generalised ledger (R2_ledger.md s5.2, `r2/dchain_amp.py`, `r2/dchain_cap.py`).

Per unit of selected volume: simple (1,6,1), doubled (2,6,1).  Two supply models:
  share    : a fraction phi of every selected width is doubled  -> (e,c,r) = (1+phi, 6, 1)
  capacity : the first UD (absolute, log_U) of every step's selection is doubled  (u_d = min(UD, u))
Gates changed exactly as R2 s5.2 / dchain_cap.py:
  dens  q = f L0 A (E + u_d/u) / (dL (1+Dv) + (C B0 - R L0) A)
  H = 1 - C u, retained width w - R u, retained_cap c0 H - (w - R u), high_deriv 25/24 H - (B - (L-1) w - R u)
  highJ = (1-rho) - nu B + nu (L-1) w - (C (1-rho) - nu R - E) u + u_d ;  marked gain gainC(nu,B0,L0,c0, w - R u, H)
  terminal gates (principal, second_ref, second_diag, ref_upper) unchanged (R2's hypothesis);
  dens capped at 3/4 - 2e-6 as in R2 (never active at e = 1 on this chain).
usage: python3 dchain.py MODE PAR out.json   (MODE = share|cap; PAR = phi or UD)
"""
import sys, os, json, time
import numpy as np
TA = '/home/user/QuasiRiemannTracker/research/newpowers/ta'
sys.path.insert(0, TA)
import chain2 as C2  # noqa: E402


KAPPA_I = 0.74963782          # incumbent natural exponent of the source theorem (sources.tex: theta_I = 0.87481891)
L_BOOT = 2.5715


class DCfg(C2.Cfg):
    def __init__(self, E=1.0, C=6.0, R=1.0, UD=0.0, retained=False, native=False, r2=False, **kw):
        super().__init__(**kw)
        self.E, self.C, self.R, self.UD, self.retained, self.native, self.r2 = E, C, R, UD, retained, native, r2


def highJ_gen(B, L, w, u, nu, E, C, R):
    m = C2.one_minus_rho(nu)
    return m - nu * B + nu * (L - 1.0) * w - (C * m - nu * R - E) * u


def gmin(cfg, B0, L0, c0, s0, A, D, N=None, full=False, nuf=None):
    dL = cfg.dL
    B = B0 - s0 * dL
    L = L0 - dL
    c = cfg.cchild
    vmax = c - s0
    if vmax <= 0:
        return None, vmax
    N = cfg.N if N is None else N
    t = np.linspace(0, 1, N) ** 3
    v = vmax * t
    w = s0 + v
    u = A * v / (1 + D * v)
    ud = np.minimum(cfg.UD, u)
    ratio = np.where(u > 0, ud / np.maximum(u, 1e-300), 1.0 if cfg.UD > 0 else 0.0)
    den = dL * (1 + D * v) + (cfg.C * B0 - cfg.R * L0) * A
    if cfg.r2:   # doubled units counted by norm in the face: width removed r = 2 per doubled unit (R2 s5.5 'phi_r2')
        den = den - L0 * A * ratio
    q = cfg.dfac * L0 * A * (cfg.E + ratio) / den
    q = np.minimum(q, cfg.qmax - 2e-6)   # R2 convention: LOW holds for every smaller q; HIGH needs q <= 3/4
    H = 1 - cfg.C * u
    s_ret = w - cfg.R * u - (ud if cfg.r2 else 0.0)
    qq = np.minimum(q, cfg.qmax)
    nu = qq[:, None]
    J = highJ_gen(B, L, w[:, None], u[:, None], nu, cfg.E, cfg.C, cfg.R) + ud[:, None] * ((1.0 + nu) if cfg.r2 else 1.0)
    if cfg.retained:   # doubled slots kept for the later steps sit at HIGH rows at the natural bound kappa_I, not nu
        k = round((L_BOOT - L0) / dL)          # steps already taken = doubled capacities still carried by this object
        J = J - np.maximum(0.0, KAPPA_I - nu) * (k * cfg.UD)
        if cfg.native:  # R2 s2.3(f): a carried doubled unit lowers the packed envelope H by 2 (norm-based first radius)
            J = J - 2.0 * C2.one_minus_rho(nu) * (k * cfg.UD)
    gn = C2.marked_gain(cfg, nu, B0, L0, c0, s_ret[:, None], H[:, None])
    Jm = J + gn
    g = dict(q_lower=q - cfg.qlow, q_upper=cfg.qmax - q, q_floor=q - cfg.floor, H_lower=H - 0.9,
             retained_cap=c0 * H - s_ret, retained_width=s_ret, low=(1 - cfg.dfac) * L0 * A * (cfg.E + ratio) / (1 + D * v),
             high=Jm.min(axis=1), high_deriv=25 / 24 * H - (B - (L - 1) * w - cfg.R * u - (ud if cfg.r2 else 0.0)),
             principal=1 - B + (L - 2) * w - 4.5 * u, second_ref=0.05 + 1.5 * (1 - B) + (1.5 * L - 2.5) * w - 4.5 * u,
             second_diag=1 - B + (L - 1) * w - 4 * u, ref_upper=1 / 3 - 2 * w - 3 * u, sel_deriv=A / (1 + D * v) ** 2)
    out = {k: float(val.min()) for k, val in g.items()}
    if full:
        out['_q0'] = float(q[0])
    return out, vmax


# monkey-patch the chain machinery of chain2 to use this gmin
C2.gmin = gmin


def main():
    mode, par, out = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    if mode == 'share':
        cfg = DCfg(E=1.0 + par, gain=1.0, floor=0.5, dfac=0.999, boot=False, dL=0.005, nu_mode='q')
    elif mode == 'cap':
        cfg = DCfg(E=1.0, UD=par, gain=1.0, floor=0.5, dfac=0.999, boot=False, dL=0.005, nu_mode='q')
    elif mode == 'cap2':
        cfg = DCfg(E=1.0, UD=par, r2=True, gain=1.0, floor=0.5, dfac=0.999, boot=False, dL=0.005, nu_mode='q')
    elif mode == 'capRN':
        cfg = DCfg(E=1.0, UD=par, retained=True, native=True, gain=1.0, floor=0.5, dfac=0.999, boot=False, dL=0.005, nu_mode='q')
    elif mode == 'capR':
        cfg = DCfg(E=1.0, UD=par, retained=True, gain=1.0, floor=0.5, dfac=0.999, boot=False, dL=0.005, nu_mode='q')
    else:
        raise SystemExit('mode share|cap|capR')
    t0 = time.time()
    rows = C2.run(cfg, Lend=1.80, out=out, verbose=False)
    ok = [r for r in rows if not r.get('infeasible')]
    if not ok:
        print(mode, par, 'infeasible at the first step', flush=True); return
    print('%s %g: %d steps, end L=%.4f B=%.6f last bind=%s [%.0fs]' % (mode, par, len(ok), ok[-1]['L'], ok[-1]['B'],
          ok[-1]['bind'], time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
