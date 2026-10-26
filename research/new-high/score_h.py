"""h re-optimization of the return for a flow (P at the crossing face, C at 0.06), env as ret_new.py.
usage: python3 score_h.py FLOW.json h1,h2,... [sP]"""
import sys, os, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ret_new as RN
import score as SC
import score2 as S2
from fractions import Fraction as Fr


def theta(args):
    BP, LP, BC, LC, h, sP = args
    RS = RN.RS
    P = dict(RS.DEF); P.update(SC.DESIGN)
    P.update(BP=f'{BP:.8f}', LP=f'{LP:.8f}', BC=f'{BC:.8f}', LC=f'{LC:.8f}', h=str(h), sP=str(sP))
    P = {k: Fr(v) for k, v in P.items()}
    return RS.ts(P, lo=8650000)


if __name__ == '__main__':
    path = sys.argv[1]; hs = sys.argv[2].split(',')
    sP = sys.argv[3] if len(sys.argv) > 3 else '0.058'
    rows = json.load(open(path))
    ss = S2.crossing(rows)
    grid = sorted({round(x['s'], 6) for x in rows})
    spf = min(grid, key=lambda s: abs(s - ss))
    BP, LP = SC.face_at(rows, spf); BC, LC = SC.face_at(rows, 0.06)
    with Pool(4) as pool:
        res = pool.map(theta, [(BP, LP, BC, LC, h, sP) for h in hs])
    tag = f"kL={RN.KL} cI={RN.CI} TMAX={RN.TMAX}"
    for h, th in zip(hs, res):
        print(f"[{tag}] {os.path.basename(path)} P@{spf} sP={sP} h={h} theta*={th}", flush=True)
