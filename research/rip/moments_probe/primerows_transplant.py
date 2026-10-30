"""Mask transplant: give each prime row the coprimality mask of randomly chosen composite rows, keep its own character.

For a prime row u = pi and a composite row v with mask set M(v) (factors of v that can divide a source):
    A_{u,v} = sum_{n coprime to M(v)} w(N(n)/N) chi_pi(n)
Its surrogate has the same distribution as v's surrogate, so E_v[sur(v)] (from the run file, K replicas per row) is the
correct comparator, identical in expectation to the composite class's.  If the prime/composite gap in actual/surrogate is
caused by the mask (the way the surrogate reacts to it), then  mean|A|^6 / mean sur(v)  must equal the composite class
ratio; a property intrinsic to prime moduli would keep it at the prime-row value.
Also reported: the same with masks drawn only from composite rows whose smallest factor has norm 7 (resp. 13), against
the corresponding composite subclass.
usage: python3 -I primerows_transplant.py logsP/run_3e5.npz --J 4
"""
import sys, os, time, argparse, json
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import probeB as PB
import primerows_core as PC

Z6 = PC.Z6


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('npz')
    ap.add_argument('--J', type=int, default=4, help='masks per prime row')
    ap.add_argument('--seed', type=int, default=9)
    ap.add_argument('--nb', type=int, default=400)
    ap.add_argument('--out', default=None)
    ap.add_argument('--pools', nargs='+', default=['composite', 'min7', 'min13', 'minge19'])
    ap.add_argument('--saverows', default=None, help='npz with per-prime-row transplanted |A|^6 and surrogate (mean over J)')
    a = ap.parse_args()
    t0 = time.time()
    d = np.load(a.npz)
    B = int(d['B']); ms = [float(x) for x in d['ms']]; K = int(d['K'])
    st = PC.Setup(B, ms, str(d['weight']))
    assert np.array_equal(st.normu, d['normu'])
    mass = d['mass']
    S = d['S']; s6 = d['acc'][:, :, 2, :].sum(-1) / K
    a2 = np.abs(S) ** 2 / mass
    rng = np.random.default_rng(a.seed)
    nf = st.nf; minn = st.minnorm
    prim = np.flatnonzero(nf == 1)
    pools = dict(composite=np.flatnonzero(nf >= 2), min7=np.flatnonzero((nf >= 2) & (minn == 7)),
                 min13=np.flatnonzero((nf >= 2) & (minn == 13)), minge19=np.flatnonzero((nf >= 2) & (minn >= 19)))
    exb = (st.Ex[:, :st.nI] > 0)
    Wc = st.W.astype(np.complex64)
    res = {}
    cl = PC.pair_clusters(st.conj)
    rb = np.random.default_rng(1)

    def boot_pair(n1, d1, n2, d2, clus):
        """paired bootstrap of log(sum n1/sum d1) - log(sum n2/sum d2) over clusters of the same rows."""
        _, inv = np.unique(clus, return_inverse=True)
        nc = inv.max() + 1
        T = [np.bincount(inv, weights=x, minlength=nc) for x in (n1, d1, n2, d2)]
        out = []
        for _ in range(a.nb):
            w = np.bincount(rb.integers(0, nc, nc), minlength=nc).astype(float)
            out.append(np.log((w @ T[0]) / (w @ T[1])) - np.log((w @ T[2]) / (w @ T[3])))
        return np.array(out)

    def boot(num, den, clus):
        _, inv = np.unique(clus, return_inverse=True)
        nc = inv.max() + 1
        tn = np.bincount(inv, weights=num, minlength=nc); td = np.bincount(inv, weights=den, minlength=nc)
        out = []
        for _ in range(a.nb):
            w = np.bincount(rb.integers(0, nc, nc), minlength=nc).astype(float)
            out.append((w @ tn) / (w @ td))
        return np.array(out)

    # phases of the prime rows (chunks), then each assigned mask
    saved = {}
    for pname, pool in pools.items():
        if pname not in a.pools:
            continue
        V = pool[rng.integers(0, len(pool), size=(len(prim), a.J))]       # assigned composite rows
        A6 = np.zeros((len(prim), a.J, len(ms))); A2 = np.zeros_like(A6)
        for i0 in range(0, len(prim), 1500):
            idx = prim[i0:i0 + 1500]
            E, Z = PB.sextic_table(PC.subPI(st.PI, np.array([st.rows[i][0] for i in idx])), st.SA, st.SB)
            ph = Z6[E.astype(np.int64)] * (~Z)
            for j in range(a.J):
                live = np.ones((len(idx), st.nS), bool)
                for t, v in enumerate(V[i0:i0 + 1500, j]):
                    for f in st.maskkey[v]:
                        live[t] &= ~exb[:, f]
                x = np.abs((ph * live) @ Wc).astype(np.float64) ** 2 / mass
                A2[i0:i0 + 1500, j] = x; A6[i0:i0 + 1500, j] = x ** 3
        sv = s6[V]                                                         # prime rows x J x nm
        saved[pname + '_A6'] = A6.mean(1); saved[pname + '_sv'] = sv.mean(1)
        print(f'\n[{pname}] pool {len(pool)} rows, {a.J} masks per prime row ({time.time()-t0:.1f}s)')
        print('   m     prime: act/sur   transplanted: act/sur (se)   log(transpl/prime) paired (se)   pool (genuine): act/sur (se)   log(transpl/genuine) (se)   M2 transpl/genuine')
        res[pname] = []
        for im, m in enumerate(ms):
            rp = (a2[prim, im] ** 3).mean() / s6[prim, im].mean()
            bt = boot(A6[:, :, im].mean(1), sv[:, :, im].mean(1), cl[prim])
            rt = A6[:, :, im].mean() / sv[:, :, im].mean()
            bg = boot(a2[pool, im] ** 3, s6[pool, im], cl[pool])
            rg = (a2[pool, im] ** 3).mean() / s6[pool, im].mean()
            ld = np.log(rt / rg); sld = np.std(np.log(bt) - np.log(bg))
            bpp = boot_pair(A6[:, :, im].mean(1), sv[:, :, im].mean(1), a2[prim, im] ** 3, s6[prim, im], cl[prim])
            lp = np.log(rt / rp)
            res[pname].append(dict(m=m, prime=rp, transplant=rt, transplant_se=float(np.std(bt)), genuine=rg, genuine_se=float(np.std(bg)),
                                   logdiff=ld, logdiff_se=sld, M2t=float(A2[:, :, im].mean()), M2g=float(a2[pool, im].mean()),
                                   log_tp=lp, log_tp_se=float(np.std(bpp)),
                                   act_t=float(A6[:, :, im].mean()), act_p=float((a2[prim, im] ** 3).mean()), sur_t=float(sv[:, :, im].mean()),
                                   sur_p=float(s6[prim, im].mean()), M2p=float(a2[prim, im].mean())))
            print(f'   {m:.2f}  {rp:.3f}            {rt:.3f} ({np.std(bt):.3f})            {lp:+.3f} ({np.std(bpp):.3f})                    {rg:.3f} ({np.std(bg):.3f})                 {ld:+.3f} ({sld:.3f})'
                  f'              {A2[:, :, im].mean():.3f}/{a2[pool, im].mean():.3f}', flush=True)
    if a.out:
        json.dump(dict(args=vars(a), results=res), open(a.out, 'w'), indent=1, default=float)
    if a.saverows:
        np.savez_compressed(a.saverows, prim=prim, **saved)
    print(f'done ({time.time()-t0:.1f}s)')


if __name__ == '__main__':
    main()
