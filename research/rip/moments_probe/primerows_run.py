"""Data run for the prime/composite study: actual S_u and K surrogate replicas per row, with row metadata.
Saves an .npz consumed by primerows_analyze.py.
usage: python3 -I primerows_run.py --B 300000 --m 0.4 0.45 0.5 0.55 0.6 --K 32 --out logsP/run_3e5.npz [--rough 0] [--weight smooth]
"""
import sys, os, time, argparse, json
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import primerows_core as PC

ap = argparse.ArgumentParser()
ap.add_argument('--B', type=int, required=True)
ap.add_argument('--m', type=float, nargs='+', required=True)
ap.add_argument('--K', type=int, default=16)
ap.add_argument('--groups', type=int, default=4)
ap.add_argument('--keep', type=int, default=4)
ap.add_argument('--weight', default='smooth')
ap.add_argument('--rough', type=int, default=0)
ap.add_argument('--seed', type=int, default=11)
ap.add_argument('--out', required=True)
a = ap.parse_args()
t0 = time.time()
st = PC.Setup(a.B, a.m, a.weight, rough=a.rough)
S = st.actual()
rng = np.random.default_rng(a.seed)
acc, kept = st.surrogate(a.K, rng, groups=a.groups, keep=a.keep)
np.savez_compressed(a.out, B=a.B, ms=np.array(a.m), K=a.K, weight=a.weight, rough=a.rough, mass=st.mass,
                    S=S.astype(np.complex64), acc=acc.astype(np.float64), kept=kept, diag=st.diag,
                    nf=st.nf, normu=st.normu, kres=st.kres, minnorm=st.minnorm, minidx=st.minidx,
                    has_inert=st.has_inert, conj=st.conj, selfconj=st.selfconj, has_pair=st.has_pair,
                    maxsrc=st.maxsrc, nS=st.nS,
                    maskkey=np.array([','.join(map(str, k)) for k in st.maskkey]),
                    minkind=st.PI['kind'][st.minidx], factors=np.array([','.join(map(str, r)) for r in st.rows]),
                    PInorm=st.PI['norm'], PIkind=st.PI['kind'], PIp=st.PI['p'])
print(f'saved {a.out} ({time.time()-t0:.1f}s)', flush=True)
