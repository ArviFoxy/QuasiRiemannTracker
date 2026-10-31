# Price a width-restricted count face properly: the new face (Bn, Ln, capn) is claimed only for slot widths >= s0.
# Plain curve: Z(m) = min(capn, (Bn-2m)/Ln) for m <= m_s = (Bn - s0*Ln)/2, base face beyond.
# Window needs plainCurve(m) <= value beyond the witness: guard v_new >= P_base(m_s) (P_base decreasing in m),
# and the witness must lie in the new-face region (z at witness >= s0). Otherwise fall back to the base face count.
import sys, io, contextlib
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/second/base_models')
with contextlib.redirect_stdout(io.StringIO()):
    import worth, fast, ideal
import numpy as np
from ideal import face_count
fast.branch = worth.make_branch(5/6); ideal.branch = fast.branch
BASE = (0.99999, 2.0001, 0.134284)
d = np.round(np.arange(0.30, 0.60, 0.0005), 6)
p = np.round(np.array([0.45, 0.48, 0.49, 0.495, 0.499, 0.5]), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')

def witness(B, L, cap):
    bs = fast.branch(DD, PP, B, L, cap, np.zeros_like(DD, bool)); bc = fast.branch(DD, PP, B, L, cap, np.ones_like(DD, bool))
    vs = bs['N']/bs['J']; vc = bc['N']/bc['J']; use_c = vc >= vs
    b = {k: np.where(use_c, bc[k], bs[k]) for k in bs}
    t = b['T']/b['J']; r = b['RN']/b['DJ']; m = t - r
    z = np.where(use_c, cap, (B - 2*m)/L)
    return m, z

def env_restricted(Ln, capn, s0, Bn=0.99999, mode='strict'):
    okb, vb = face_count(DD, PP, *BASE); envb = np.where(okb, vb, np.inf)
    if s0 is None:
        okn, vn = face_count(DD, PP, Bn, Ln, capn); return np.minimum(envb, np.where(okn, vn, np.inf)), None
    okn, vn = face_count(DD, PP, Bn, Ln, capn)
    m, z = witness(Bn, Ln, capn)
    ms = (Bn - s0*Ln)/2
    Bb, Lb, cb = BASE
    Pb = 1 - 2*DD*ms - 2*DD*PP*np.minimum(cb, (Bb - 2*ms)/Lb)
    good = okn & (z >= s0) & (vn >= Pb)
    if mode == 'strict':
        envn = np.where(good, vn, np.inf)
    else:  # value max(v_new, P_base(m_s)) when only the jump guard fails (approximate)
        envn = np.where(okn & (z >= s0), np.maximum(vn, Pb), np.inf)
    return np.minimum(envb, envn), (good, z, Pb, vn)

def theta(env, h=0.8097, numCap=0.075, Bp=0.99999, Lp=2.0001, reserve=1e-8):
    lo, hi = 0.86, 0.885
    for _ in range(50):
        th = (lo+hi)/2; c = 1-th; ell = 4*c-1/3; y = h-2*ell; kappa = 1-2*c; dd = h+1e-10
        Cc = min(numCap*dd, (2*y-(2-Bp)*dd)/Lp)
        e = np.minimum(env, worth.old_count(DD, PP, kappa, 5/6))
        E = 0.5+13*h/75-y/2-ell/2-0.09*dd+DD/2+DD*PP*(ell-Cc/2)+0.75*dd*e
        if E.max() > th-reserve: lo = th
        else: hi = th
    k = np.unravel_index(np.argmax(E), E.shape)
    return hi, DD[k], PP[k]

PR99 = 0.8733819666; bar = PR99 - 5e-5
t0 = theta(env_restricted(2.0001, 0.134284, None)[0])
print('base: theta %.8f (bank)  bind d %.4f p %.3f' % t0)
if __name__ == '__main__':
    faces = [(1.92, 0.1407), (1.90, 0.1435), (1.88, 0.1477)]
    for Ln, capn in faces:
        tu = theta(env_restricted(Ln, capn, None)[0])
        print('face Lambda %.2f cap %.4f unrestricted: theta %.8f  vs bar %+.2e' % (Ln, capn, tu[0], tu[0]-bar))
        for s0 in (0.135, 0.13, 0.1295, 0.129, 0.128, 0.127, 0.125, 0.12, 0.11, 0.10):
            for mode in ('strict', 'max'):
                env, info = env_restricted(Ln, capn, s0, mode=mode)
                t = theta(env)
                print('   s0 %.4f %-6s theta %.8f vs PR99 %+.2e vs bar %+.2e  bind d %.4f p %.3f' % (s0, mode, t[0], t[0]-PR99, t[0]-bar, t[1], t[2]))
