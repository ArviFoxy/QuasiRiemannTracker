import numpy as np
from fast import branch, old_count
from ideal import face_count, E_newtop, theta_star
src = (0.99999, 2.02, 0.13309)
d = np.round(np.arange(0.20, 0.75, 0.0005), 6)
p = np.round(np.concatenate([np.arange(0.0, 0.49, 0.01), [0.49, 0.495, 0.499, 0.5]]), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')
ok, v = face_count(DD, PP, *src)
env = np.where(ok, v, np.inf)
th, k, oc = theta_star(DD, PP, env)
print('theta* = %.8f' % th)
E, oc = E_newtop(th, DD, PP, env)
# profile at p = 1/2
j = -1
bs = branch(d, 0.5, *src, False); bc = branch(d, 0.5, *src, True)
vs = bs['N'] / bs['J']; vc = bc['N'] / bc['J']
ms = (bs['T'] / bs['J'] - bs['RN'] / bs['DJ']); mc = (bc['T'] / bc['J'] - bc['RN'] / bc['DJ'])
mstar = (src[0] - src[1] * (src[2] - 1e-7)) / 2
print('kink m* = %.5f' % mstar)
for i in range(0, len(d), 20):
    piece = 'cap' if vc[i] >= vs[i] else 'slope'
    print('d=%.3f excess=%+.3e  v_slope=%.5f (m=%.4f) v_cap=%.5f (m=%.4f) piece=%s old=%.5f t=%.4f r=%.4f' % (
        d[i], E[i, j] - (th - 1e-8), vs[i], ms[i], vc[i], mc[i], piece, oc[i, j],
        (bc['T'] / bc['J'])[i] if piece == 'cap' else (bs['T'] / bs['J'])[i],
        (bc['RN'] / bc['DJ'])[i] if piece == 'cap' else (bs['RN'] / bs['DJ'])[i]))
# max excess per p
print('max excess per p (top 6):')
mx = E.max(axis=0) - (th - 1e-8)
for jj in np.argsort(-mx)[:6]:
    print('  p=%.3f max excess %.3e at d=%.4f' % (p[jj], mx[jj], d[np.argmax(E[:, jj])]))
