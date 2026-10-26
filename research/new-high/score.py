"""Score flows with the exact return (../mixed-step/ret_scan.py: Lemma D, dMinus > 1/2).

Faces are read from a flow json at s (B = E + L s, L); P is scanned over SP_LIST and C is taken at
SC_FACE.  Fixed return design: cap = 0.075, sP = 0.058, sC = 0.058, h = 0.8044.
usage: python3 score.py FLOW.json [FLOW2.json ...]      (prints best theta* per flow)
"""
import sys, os, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mixed-step'))
from fractions import Fraction as Fr

SP_LIST = [0.0565, 0.057, 0.0575, 0.058]
SC_FACE = 0.06
DESIGN = dict(cap='0.075', sP='0.058', sC='0.058', h='0.8044')


def face_at(rows, s):
    for r in rows:
        if abs(r['s'] - s) < 1e-9:
            return r['E'] + r['L']*r['s'], r['L']
    raise KeyError(s)


def theta(args):
    BP, LP, BC, LC = args
    import ret_scan as RS
    P = dict(RS.DEF)
    P.update(DESIGN)
    P.update(BP=f'{BP:.8f}', LP=f'{LP:.8f}', BC=f'{BC:.8f}', LC=f'{LC:.8f}')
    P = {k: Fr(v) for k, v in P.items()}
    return RS.ts(P)


def jobs_for(path):
    rows = json.load(open(path))
    BC, LC = face_at(rows, SC_FACE)
    out = []
    for s in SP_LIST:
        BP, LP = face_at(rows, s)
        out.append((path, s, (BP, LP, BC, LC)))
    return out


if __name__ == '__main__':
    jobs = []
    for f in sys.argv[1:]:
        jobs += jobs_for(f)
    with Pool(4) as pool:
        res = pool.map(theta, [j[2] for j in jobs])
    best = {}
    for (path, s, a), th in zip(jobs, res):
        print(f"{os.path.basename(path)} sP_face={s} BP={a[0]:.7f} LP={a[1]:.5f} BC={a[2]:.7f} LC={a[3]:.5f} theta*={th}", flush=True)
        if th is not None and (path not in best or th < best[path][0]):
            best[path] = (th, s)
    for path, (th, s) in best.items():
        print(f"BEST {os.path.basename(path)}: theta* = {th/1e7:.7f} (P face at s={s})")
