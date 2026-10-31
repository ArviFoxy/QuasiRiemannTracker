import sys, numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/selected-leaf')
import root_ledger as R
BASE = (0.99999, 2.0001, 0.134284)
def run_from_base(K, B=0.99999, h=1e-5, c6=6.0, base=BASE):
    L, c = base[1], base[2]; path = [(L, c, 0.0)]
    while True:
        Ln = L - h; den = L*(1 + K) - c6*K*B
        if den <= 0: return L, c, 'overshoot', path
        a = K*h/den*(1 + 1e-9)
        if a > (Ln - 1)/(c6 - 2): return L, c, 'selected branch', path
        cn = c/(1 - a + c6*a*c)*(1 - 1e-12); S = cn
        g = min((1 + S)/2, 3/4 - S, (6 + S)/11)
        ok = {'principal': (3/4 + g/2 - B) + (Ln - 2)*S - 4.5*a*S > 0, 'diagonal': Ln - 1 - 4*a > 0,
              'secondRef': 1.5*Ln - 2.5 - 4.5*a > 0, 'refPos': 1/6 - (1 + 1.5*a)*cn > 0, 'H': 1 - c6*a*cn > 0, 'cap_lt': c < 1/6}
        bad = [k for k, v in ok.items() if not v]
        if bad: return L, c, ','.join(bad), path
        L, c = Ln, cn; path.append((L, c, a))
def gam(x, mode):
    if mode == 'perrange': return np.maximum(0.0, 17*x/18 - 5/6)
    if mode == 'fullsieve': return np.maximum(0.0, 5*x/18 - 1/6)
    if mode == 'theta6': return np.maximum(0.0, x/6)   # crude stand-in
    return float(mode)*np.ones_like(x)
def e_sel_x(x1, x2, s, M, delta, mode, nrho=241):
    rho = np.linspace(0.0, M/6, nrho); y = M - 6*rho
    ok = (y >= x1) & (y >= x2) & (y > 0)
    xe = np.minimum(x1, y - x1) + np.minimum(x2, y - x2) + s
    g = gam(np.where(y > 0, xe/np.maximum(y, 1e-12), 0), mode)
    per = np.maximum(xe, (1 - delta + g)*y + delta*xe)
    return np.where(ok, rho + per, -1e9).max()
def worst(B, L, c, a, L0, c0, delta, mode, s0, nS=81, nt=9, base=BASE):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        if S < s0: continue
        w = S; u = a*w; PCmax = B - L*S
        for PC in np.linspace(0.5*PCmax, PCmax, 6):
            for s in (w - u, 0.9*(w-u), 0.75*(w - u), 0.5*(w - u), 0.25*(w-u), 0.1*(w-u)):
                for t in np.linspace(0.0, 1 + 6*u, nt):
                    M = 1 + t - 6*u
                    for frac in (0.5, 0.45, 0.4, 0.3, 0.0):
                        x1, x2 = PC*(1 - frac), PC*frac
                        sel = e_sel_x(x1, x2, s, M, delta, mode) - M
                        par = R.deletion_need(B, L0, c0, PC, s, M) if s >= s0 else R.deletion_need(base[0], base[1], base[2], PC, s, M)
                        v = min(sel, par) - u
                        if v > wv: wv, where = v, (round(S,4), round(s,4), round(M,4), round(x1,3), round(x2,3), round(sel,5), round(par,6), u)
    return wv, where
def worst2(B, L, c, a, L0, c0, delta, gamma, s0, nS=81, nt=9, base=BASE, fracs=(0.5, 0.45, 0.4, 0.3, 0.0)):
    """uniform excess gamma; restricted parent valid only if the width left after its deletion is >= s0, else base face"""
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        if S < s0: continue
        w = S; u = a*w; PCmax = B - L*S
        for PC in np.linspace(0.5*PCmax, PCmax, 6):
            for s in (w - u, 0.95*(w-u), 0.9*(w-u), 0.75*(w - u), 0.5*(w - u), 0.25*(w-u), 0.1*(w-u)):
                for t in np.linspace(0.0, 1 + 6*u, nt):
                    M = 1 + t - 6*u
                    pr = R.deletion_need(B, L0, c0, PC, s, M)
                    par = pr if (s - pr) >= s0 else R.deletion_need(base[0], base[1], base[2], PC, s, M)
                    for frac in fracs:
                        x1, x2 = PC*(1 - frac), PC*frac
                        sel = e_sel_x(x1, x2, s, M, delta, gamma) - M
                        v = min(sel, par) - u
                        if v > wv: wv, where = v, (round(S,4), round(s,4), round(M,4), round(x1,3), round(x2,3), round(sel,5), round(par,6), u)
    return wv, where
def e_sel_geo(x1, x2, s, M, delta, Delta, kind='perrange', nrho=241):
    rho = np.linspace(0.0, M/6, nrho); y = M - 6*rho
    ok = (y >= x1) & (y >= x2) & (y > 0)
    xe = np.minimum(x1, y - x1) + np.minimum(x2, y - x2) + s
    x = np.where(y > 0, xe/np.maximum(y, 1e-12), 0)
    if kind == 'perrange': g = np.maximum(0.0, 17*x/18 - 5/6 - Delta)
    else: g = np.maximum(0.0, (5*x - 3)/18 - Delta)
    per = np.maximum(xe, (1 - delta + g)*y + delta*xe)
    return np.where(ok, rho + per, -1e9).max()
def worst_geo(B, L, c, a, L0, c0, delta, Delta, s0, kind='perrange', nS=41, nt=7, base=BASE):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        if S < s0: continue
        w = S; u = a*w; PCmax = B - L*S
        for PC in np.linspace(0.5*PCmax, PCmax, 5):
            for s in (w - u, 0.9*(w-u), 0.75*(w - u), 0.5*(w - u), 0.25*(w-u)):
                for t in np.linspace(0.0, 1 + 6*u, nt):
                    M = 1 + t - 6*u
                    pr = R.deletion_need(B, L0, c0, PC, s, M)
                    par = pr if (s - pr) >= s0 else R.deletion_need(base[0], base[1], base[2], PC, s, M)
                    for frac in (0.5, 0.4, 0.3, 0.0):
                        x1, x2 = PC*(1 - frac), PC*frac
                        sel = e_sel_geo(x1, x2, s, M, delta, Delta, kind) - M
                        v = min(sel, par) - u
                        if v > wv: wv, where = v, (round(S,4), round(s,4), round(M,4), round(x1,3), round(x2,3))
    return wv, where
def e_sel_geo2(x1, x2, s, M, delta, Delta, nrho=241):
    """per root: better of (selected norm with excess (5x-3)/18 - Delta) and (full bilinear sieve max(y, xe, 5y/6+5xe/18) - Delta*y)"""
    rho = np.linspace(0.0, M/6, nrho); y = M - 6*rho
    ok = (y >= x1) & (y >= x2) & (y > 0)
    xe = np.minimum(x1, y - x1) + np.minimum(x2, y - x2) + s
    x = np.where(y > 0, xe/np.maximum(y, 1e-12), 0)
    g = np.maximum(0.0, (5*x - 3)/18 - Delta)
    sel = np.maximum(xe, (1 - delta + g)*y + delta*xe)
    full = np.maximum(np.maximum(y, xe), 5*y/6 + 5*xe/18 - Delta*y)
    per = np.minimum(sel, full)
    return np.where(ok, rho + per, -1e9).max()
def worst_geo2(B, L, c, a, L0, c0, delta, Delta, s0, nS=41, nt=7, base=BASE):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        if S < s0: continue
        w = S; u = a*w; PCmax = B - L*S
        for PC in np.linspace(0.5*PCmax, PCmax, 5):
            for s in (w - u, 0.9*(w-u), 0.75*(w - u), 0.5*(w - u), 0.25*(w-u)):
                for t in np.linspace(0.0, 1 + 6*u, nt):
                    M = 1 + t - 6*u
                    pr = R.deletion_need(B, L0, c0, PC, s, M)
                    par = pr if (s - pr) >= s0 else R.deletion_need(base[0], base[1], base[2], PC, s, M)
                    for frac in (0.5, 0.4, 0.3, 0.0):
                        x1, x2 = PC*(1 - frac), PC*frac
                        sel = e_sel_geo2(x1, x2, s, M, delta, Delta) - M
                        v = min(sel, par) - u
                        if v > wv: wv, where = v, (round(S,4), round(s,4), round(M,4), round(x1,3), round(x2,3))
    return wv, where
def e_sel_geo3(x1, x2, s, M, delta, Delta, nrho=241):
    """'with C': selected-norm excess = per-twist-range source-term shortfall (17x/18 - 5/6 - Delta)_+;
    per root take the better of that and the full bilinear sieve max(y, xe, 5y/6+5xe/18)"""
    rho = np.linspace(0.0, M/6, nrho); y = M - 6*rho
    ok = (y >= x1) & (y >= x2) & (y > 0)
    xe = np.minimum(x1, y - x1) + np.minimum(x2, y - x2) + s
    x = np.where(y > 0, xe/np.maximum(y, 1e-12), 0)
    g = np.maximum(0.0, 17*x/18 - 5/6 - Delta)
    sel = np.maximum(xe, (1 - delta + g)*y + delta*xe)
    full = np.maximum(np.maximum(y, xe), 5*y/6 + 5*xe/18)
    per = np.minimum(sel, full)
    return np.where(ok, rho + per, -1e9).max()
def worst_geo3(B, L, c, a, L0, c0, delta, Delta, s0, nS=41, nt=7, base=BASE):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        if S < s0: continue
        w = S; u = a*w; PCmax = B - L*S
        for PC in np.linspace(0.5*PCmax, PCmax, 5):
            for s in (w - u, 0.9*(w-u), 0.75*(w - u), 0.5*(w - u), 0.25*(w-u)):
                for t in np.linspace(0.0, 1 + 6*u, nt):
                    M = 1 + t - 6*u
                    pr = R.deletion_need(B, L0, c0, PC, s, M)
                    par = pr if (s - pr) >= s0 else R.deletion_need(base[0], base[1], base[2], PC, s, M)
                    for frac in (0.5, 0.4, 0.3, 0.0):
                        x1, x2 = PC*(1 - frac), PC*frac
                        sel = e_sel_geo3(x1, x2, s, M, delta, Delta) - M
                        v = min(sel, par) - u
                        if v > wv: wv, where = v, (round(S,4), round(s,4), round(M,4), round(x1,3), round(x2,3))
    return wv, where
