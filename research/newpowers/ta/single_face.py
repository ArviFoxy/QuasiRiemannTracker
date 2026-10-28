"""Best single face (count face = physical face, no role split) along a stored chain; usage: python3 single_face.py CHAIN.json [step]"""
import sys, json
import exact
import run2

if __name__ == '__main__':
    rows = json.load(open(sys.argv[1]))
    step = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    faces = run2.faces_of(rows)
    n = len(faces)
    cands = sorted(set(list(range(0, n, step)) + list(range(max(0, n - 6), n))))
    best = None
    g = 0.87397
    for i in cands:
        if faces[i][0] < 2.0:
            continue                       # the physical face needs L_P >= 2 (schedule_lambda_low)
        r = exact.theta_exact(faces[i][1], faces[i][0], faces[i][1], faces[i][0], guess=g, unit=10**8, span=300)
        t = None if r is None else r[0]
        print(i, '%.4f' % faces[i][0], t, flush=True)
        if t is not None:
            g = t
            if best is None or t < best[0]:
                best = (t, i)
    # refine
    t, i = best
    for j in range(i - 3, i + 4):
        if 0 <= j < n and faces[j][0] >= 2.0:
            r = exact.theta_exact(faces[j][1], faces[j][0], faces[j][1], faces[j][0], guess=t, unit=10**9, span=400)
            if r is not None and r[0] < best[0]:
                best = (r[0], j)
    print('best single face: idx %d L=%.4f B=%.6f theta=%.9f (gap %+.2e)' % (best[1], faces[best[1]][0], faces[best[1]][1], best[0], best[0] - run2.BAR))
