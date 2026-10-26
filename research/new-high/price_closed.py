"""Instant source-side pricing from the closed-form flow (closed_form.py): s* = width capacity at plain
length 0.843 of the best face with Lambda >= 2 (return receipt schedule_lambda_low), and the calibrated
return response d theta*/d s* (sP re-optimized to s*) from the exact scores in REPORT.md section 6.
usage: python3 price_closed.py"""
import closed_form as CF

EP = 0.843
SLOPE = None   # filled from calibration below


def s_star(kL=5/6, cI=2.0, dxi=0.0, mh=1e-4, s_end=0.068):
    rows = CF.flow(kL, cI, mh, dxi, s_end=s_end)
    best = 0.0
    for r in rows:
        if r['L'] >= 2.0:
            best = max(best, (r['B'] - EP)/r['L'])
    return best, rows


if __name__ == '__main__':
    base, _ = s_star()
    print(f"baseline s* = {base:.5f}")
    for kL in (5/6, 0.82, 0.81, 0.80, 0.78, 0.75):
        for cI in (2.0, 1.9, 1.8, 1.6):
            s, rows = s_star(kL, cI)
            qend = rows[-1]['q']
            print(f"kL={kL:.4f} cI={cI:.2f}: s*={s:.5f} (Delta s*={s-base:+.5f})  q(0.062)={[r for r in rows if abs(r['s']-0.062)<1e-9][0]['q']:.4f}")
