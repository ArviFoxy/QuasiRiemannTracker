"""HIGH gain in the source step with/without repeated inverse marks (Lemma 8.1 overlap adapter).
Natural plain face (2m + (9/2) z <= 1), row width Q=1, density nu, available marked width S, amplitude p.
count(p) = min_t max_{(r,m): r+m=t, r<=t, m<=1/2} min(line_inv_or_long(r), line_plain(m)).
mass(p) = count(p) + 2 p nu S.  Gate quantity: G_eff = max_p ... ; we report rho - max_p(mass(p)) + nu S."""
import numpy as np

def count_p(nu, S, p, rep, B=1.0, Lam=4.5, hcap=1.0, ts=np.linspace(1.0, 1.5, 501), nr=2001, al=5/6):
    best = np.inf
    for t in ts:
        r = np.linspace(max(t-0.5, 0), t, nr); m = t - r
        zI = (1-r)/2 if rep else np.minimum(S, (1-r)/2)
        zI = np.maximum(zI, 0)
        inv = np.where(r < 1, 1 - nu*(r + 2*p*zI), (1-al) + (al-nu)*r)
        zP = np.maximum(np.minimum(np.minimum(S, hcap), (B - 2*m)/Lam), 0)
        pl = 1 - nu*(2*m + 2*p*zP)
        c = np.minimum(inv, pl)
        v = c.max()
        if v < best: best = v
    return best

def report(nu, S):
    xi0 = 10/(3*(5-2*nu)); rho = 1 - nu*xi0
    ps = np.linspace(0, 0.5, 26)
    out = {}
    for rep in (False, True):
        mass = [count_p(nu, S, p, rep) + 2*p*nu*S for p in ps]
        k = int(np.argmax(mass))
        out[rep] = (rho - max(mass) + nu*S, ps[k])
    return rho, out

if __name__ == "__main__":
    for nu in (0.5, 0.55, 0.6, 0.65, 0.7, 0.75):
        for S in (0.03, 0.05):
            rho, out = report(nu, S)
            w = 5-6*nu; d = 5-2*nu
            phi = nu*w/d; A = 14*nu*w/(115-54*nu); Bn = 2*nu*w*w/(3*d*(115-54*nu)); C = 16*nu*w*w/(3*d*(185-138*nu))
            G = min(phi*S, A*S+Bn, C)
            print(f"nu={nu:.2f} S={S:.2f} rho={rho:.5f}  G_LD2={G:.5f}  Geff(norep)={out[False][0]:.5f}@p={out[False][1]:.2f}  Geff(rep)={out[True][0]:.5f}@p={out[True][1]:.2f}")
