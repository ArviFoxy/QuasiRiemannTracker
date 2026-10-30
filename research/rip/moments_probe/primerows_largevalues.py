"""Large values versus the value at the smallest prime ideal (norm 7), prime rows only (no mask), actual vs surrogate.

For the random model the sixth moment is carried by draws with f(pi_7) = 1 (multiplicative chaos: the local factor at 7);
removing pi_7 (the mask of the commonest composite rows) removes that share.  If the actual family's moment depends less on
chi_u(pi_7) in the functional-equation regime, masking 7 costs the actual less than the surrogate -> the class gap.
Reported per m: M6 conditional on Re chi(pi_7) in {1, 1/2, -1/2, -1} (actual over prime rows, surrogate over D draws),
the share of sum |S|^6 from rows with chi(pi_7) = 1, and the same for the pair of conjugate ideals above 7.
usage: python3 -I primerows_largevalues.py --B 100000 --m 0.3 0.5 0.6 0.7 --D 400000
"""
import sys, os, time, argparse, json
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import probeB as PB
import primerows_core as PC

Z6 = PC.Z6

ap = argparse.ArgumentParser()
ap.add_argument('--B', type=int, required=True)
ap.add_argument('--m', type=float, nargs='+', required=True)
ap.add_argument('--D', type=int, default=400000)
ap.add_argument('--seed', type=int, default=4)
ap.add_argument('--out', default=None)
a = ap.parse_args()
t0 = time.time()
st = PC.Setup(a.B, a.m, 'smooth')
PI = st.PI
prim = np.flatnonzero(st.nf == 1)
j7 = np.flatnonzero(PI['norm'] == 7)                      # the two ideals above 7 (indices 0, 1)
# actual S and chi_u(pi_7), chi_u(pi7bar) for prime rows: symbol of the generator of pi_7 modulo u
S = np.zeros((len(prim), len(st.lens)), dtype=np.complex128)
e7 = np.zeros((len(prim), 2), dtype=np.int64)
Wc = st.W.astype(np.complex64)
g7A = PI['a'][j7].astype(np.int64); g7B = PI['b'][j7].astype(np.int64)
for i0 in range(0, len(prim), 2000):
    idx = prim[i0:i0 + 2000]
    sub = PC.subPI(PI, np.array([st.rows[i][0] for i in idx]))
    E, Z = PB.sextic_table(sub, st.SA, st.SB)
    S[i0:i0 + 2000] = (Z6[E.astype(np.int64)] * (~Z)) @ Wc
    E7, _ = PB.sextic_table(sub, g7A, g7B)
    e7[i0:i0 + 2000] = E7.astype(np.int64)
a2 = np.abs(S) ** 2 / st.mass
# surrogate: f at the source primes; column index of pi_7 in Ex is j7 (prefix property)
rng = np.random.default_rng(a.seed)
nIx = st.Ex.shape[1]
s2 = []; f7 = []
for n0 in range(0, a.D, 4000):
    k = min(4000, a.D - n0)
    J = rng.integers(0, 6, size=(nIx, k))
    F = Z6[np.rint(np.asarray(st.ExS @ J.astype(np.float32))).astype(np.int64) % 6]
    s2.append(np.abs(F.T @ Wc).astype(np.float64) ** 2 / st.mass)
    f7.append(J[j7].T)
s2 = np.concatenate(s2); f7 = np.concatenate(f7)
print(f'B={a.B} prime rows {len(prim)}, surrogate draws {a.D} ({time.time()-t0:.1f}s)')
# primary generators of pi_7: chi_u(pi_7) for the ideal = chi_u(primary generator) up to the global sign chi_u(-1);
# for the class statistics we use the exponent class mod 6 of chi_u(-g7) (= ideal character value, see PRIMEROWS.md)
km1 = ((st.normu[prim] - 1) // 6) % 6 * 3 % 6                 # exponent of chi_u(-1) = (-1)^k  -> 3k mod 6
ideal7 = (e7 + km1[:, None]) % 6
res = []
print(' m     | M6 act | share of sum|S|^6 from chi(pi7)=1 rows: act / sur (uniform 1/6 = 0.167) | M6 | Re chi(pi7) = 1, 1/2, -1/2, -1:  act ; sur'
      ' | share from chi(pi7) = chi(pi7bar) = 1: act / sur (1/36 = 0.028)')
for im, m in enumerate(st.ms):
    x6 = a2[:, im] ** 3; y6 = s2[:, im] ** 3
    sh_a = x6[ideal7[:, 0] == 0].sum() / x6.sum(); sh_s = y6[f7[:, 0] == 0].sum() / y6.sum()
    sh2_a = x6[(ideal7[:, 0] == 0) & (ideal7[:, 1] == 0)].sum() / x6.sum()
    sh2_s = y6[(f7[:, 0] == 0) & (f7[:, 1] == 0)].sum() / y6.sum()
    ca = []; cs = []
    for ks in ((0,), (1, 5), (2, 4), (3,)):
        ca.append(x6[np.isin(ideal7[:, 0], ks)].mean()); cs.append(y6[np.isin(f7[:, 0], ks)].mean())
    res.append(dict(m=m, M6a=x6.mean(), M6s=y6.mean(), share_a=sh_a, share_s=sh_s, share2_a=sh2_a, share2_s=sh2_s,
                    cond_a=ca, cond_s=cs))
    print(f' {m:.2f}  | {x6.mean():6.3f} / {y6.mean():6.3f} | {sh_a:.3f} / {sh_s:.3f} | '
          + ' '.join(f'{v:6.2f}' for v in ca) + ' ; ' + ' '.join(f'{v:6.2f}' for v in cs) + f' | {sh2_a:.3f} / {sh2_s:.3f}', flush=True)
if a.out:
    json.dump(dict(args=vars(a), results=res), open(a.out, 'w'), indent=1, default=float)
