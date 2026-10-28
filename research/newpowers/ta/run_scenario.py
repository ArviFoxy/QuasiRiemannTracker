"""One scenario: generate the discrete chain (or ODE), evaluate exact theta* with the role split, write results/*.json"""
import sys, os, json, time
import numpy as np
import chain, split, exact
HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results'); os.makedirs(RES, exist_ok=True)
LOGS = os.path.join(HERE, 'logs')


def sid(var, floor, boot, dfac, dL, tag=''):
    return '%s_f%.2f_b%d_d%.3f_dL%s%s' % (var, floor, int(boot), dfac, ('ode' if dL == 0 else '%g' % dL), tag)


def run_discrete(var, floor, boot, dfac, dL, nC=14, shift_R=0.0, sigma=None, tag='', Lp_lo=2.20, Lp_hi=2.48):
    name = sid(var, floor, boot, dfac, dL, tag)
    fn = os.path.join(LOGS, 'chain_%s.json' % name)
    cfg = chain.Cfg(var=var, floor=floor, dfac=dfac, boot=boot, dL=dL, shift_R=shift_R, sigma=sigma)
    if os.path.exists(fn):
        rows = json.load(open(fn))
    else:
        rows = chain.run(cfg, out=fn, verbose=False)
    faces = split.chain_faces(rows)
    n = len(faces)
    c_c = list(range(max(0, n - nC), n))
    p_c = [i for i, f in enumerate(faces) if Lp_lo <= f[0] <= Lp_hi]
    # coarse P scan: every k-th so that ~10 points
    k = max(1, len(p_c) // 10)
    p_c = p_c[::k]
    res = split.best_split(faces, c_c, p_c, verbose=False)
    res.update(name=name, var=var, floor=floor, boot=boot, dfac=dfac, dL=dL, nsteps=n, end=dict(L=faces[-1][0], B=faces[-1][1]),
               last_bind=rows[-2].get('bind') if len(rows) > 1 else None,
               infeasible_at=rows[-1] if rows and rows[-1].get('infeasible') else None)
    json.dump(res, open(os.path.join(RES, 'eval_%s.json' % name), 'w'), indent=1, default=str)
    return res


if __name__ == '__main__':
    var = sys.argv[1]; floor = float(sys.argv[2]); boot = bool(int(sys.argv[3])); dfac = float(sys.argv[4]); dL = float(sys.argv[5])
    t0 = time.time()
    r = run_discrete(var, floor, boot, dfac, dL)
    print('%-34s theta=%.9f gap=%+.2e  C(L=%.4f,s0=%.4f,idx %d/%d) P(L=%.3f) [%.0fs]' % (
        r['name'], r['theta'], r['theta'] - split.BAR, r['C']['L'], r['C']['s0'], r['C']['idx'], r['nsteps'], r['P']['L'], time.time() - t0), flush=True)
