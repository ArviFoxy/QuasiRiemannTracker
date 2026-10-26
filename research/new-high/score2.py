"""Score flows with the exact return, P faces around the envelope crossing E(s) = 0.843.

For each flow: s* = crossing of the envelope E(s) with m1 + m2 = 0.843 (linear interpolation);
P faces at the grid points s*-0.001 .. s*+0.001 (step 5e-4), C faces at C_LIST.  Fixed design
cap = 0.075, sP = 0.058, sC = 0.058, h = 0.8044 (as ../mixed-step/rs4.txt).
usage: python3 score2.py FLOW.json [...]
"""
import sys, os, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import score as SC

C_LIST = [0.06]
EP = 0.843


def crossing(rows):
    for a, b in zip(rows, rows[1:]):
        if a['E'] >= EP >= b['E']:
            return a['s'] + (a['E'] - EP)/(a['E'] - b['E'])*(b['s'] - a['s'])
    return None


def jobs_for(path):
    rows = json.load(open(path))
    ss = crossing(rows)
    grid = sorted({round(x['s'], 6) for x in rows})
    if ss is None:
        ss = grid[-1]
    near = [s for s in grid if abs(s - ss) <= 0.00101]
    out = []
    for sc in C_LIST:
        BC, LC = SC.face_at(rows, sc)
        for s in near:
            BP, LP = SC.face_at(rows, s)
            out.append((path, s, sc, ss, (BP, LP, BC, LC)))
    return out


if __name__ == '__main__':
    jobs = []
    for f in sys.argv[1:]:
        jobs += jobs_for(f)
    with Pool(4) as pool:
        res = pool.map(SC.theta, [j[4] for j in jobs])
    best = {}
    for (path, s, sc, ss, a), th in zip(jobs, res):
        print(f"{os.path.basename(path)} s*={ss:.5f} P@{s} C@{sc} BP={a[0]:.7f} LP={a[1]:.5f} "
              f"BC={a[2]:.7f} LC={a[3]:.5f} theta*={th}", flush=True)
        if th is not None and (path not in best or th < best[path][0]):
            best[path] = (th, s, sc, ss)
    for path, (th, s, sc, ss) in best.items():
        print(f"BEST {os.path.basename(path)}: theta* = {th/1e7:.7f} (s*={ss:.5f}, P@{s}, C@{sc})")
