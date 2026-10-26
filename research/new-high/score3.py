"""Score flows with the exact return whose count lines are modified as in ret_new.py.

Environment QRH_KL / QRH_CI / QRH_TMAX select the return's long-line slope, inverse slot cost and the
t* admission (see ret_new.py).  P faces around the envelope crossing E = 0.843 (score2.py), C at 0.06.
usage: QRH_KL=0.8 QRH_TMAX=3/2 python3 score3.py FLOW.json [...]
"""
import sys, os, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ret_new as RN          # patches cert_return per environment
import score as SC
import score2 as S2
from fractions import Fraction as Fr


def theta(args):
    BP, LP, BC, LC = args
    RS = RN.RS
    P = dict(RS.DEF); P.update(SC.DESIGN)
    P.update(BP=f'{BP:.8f}', LP=f'{LP:.8f}', BC=f'{BC:.8f}', LC=f'{LC:.8f}')
    P = {k: Fr(v) for k, v in P.items()}
    return RS.ts(P, lo=8650000)


if __name__ == '__main__':
    jobs = []
    for f in sys.argv[1:]:
        jobs += S2.jobs_for(f)
    with Pool(4) as pool:
        res = pool.map(theta, [j[4] for j in jobs])
    best = {}
    tag = f"kL={RN.KL} cI={RN.CI} TMAX={RN.TMAX}"
    for (path, s, sc, ss, a), th in zip(jobs, res):
        print(f"[{tag}] {os.path.basename(path)} s*={ss:.5f} P@{s} C@{sc} BP={a[0]:.7f} LP={a[1]:.5f} theta*={th}", flush=True)
        if th is not None and (path not in best or th < best[path][0]):
            best[path] = (th, s)
    for path, (th, s) in best.items():
        print(f"BEST [{tag}] {os.path.basename(path)}: theta* = {th/1e7:.7f} (P@{s})")
