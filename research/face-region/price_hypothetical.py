"""Price of D8a in theta, with the return toolchain (research/density/gen_return86.py, five-branch return).

Actual effect: zero.  Every consumer evaluates balanced plain pairs (count fibers X1 = X2 = U^m; physical
numerator: the box [0, n]^2 with balanced corner (n, n); chain steps pass the child's plains to the parent),
and on the balanced slice the Cauchy-Schwarz closure equals the face region (Lean: balanced_no_gain).

Hypothetical (an unbalanced consumer that does not exist): if a consumer at total plain length P could use the
best unbalanced pair, its slot capacity would be s_CS(P) (cs_region.py) instead of s*(P).
 * count face: binds at P ~ 0.78 (rotation test below), where s_CS = s* (both squared configurations fall on
   the last face): no gain even hypothetically;
 * physical numerator: binds at the newTop edge, P = 2 plainScale(h) = 0.8512, s* = 0.05972 -> s_CS = 0.06308;
   modelled by the parallel shift of the physical face to capacity 0.0631 at P = 0.8512 (B_P = 0.993214) with
   numeratorCap = physical cap = 63/1000.
"""
import subprocess, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, '..', 'density', 'gen_return86.py')
BASE_C = '96232839/100000000,3853/2000,9999/100000'
BASE_P = '49283557/50000000,4503/2000,31/500'


def theta(count_face, phys_face, num_cap='3/50', count_src=None, phys_src=None, lo='0.87370', hi='0.87400'):
    cmd = ['python3', GEN, '--preset', 'pr86', '--branches', 'five', '--count-face', count_face,
           '--phys-face', phys_face, '--numerator-cap', num_cap, '--find-theta', lo, hi, '--h', 'auto:7']
    if count_src:
        cmd += ['--count-src', count_src]
    if phys_src:
        cmd += ['--phys-src', phys_src]
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=os.path.dirname(GEN))
    out = (r.stdout + r.stderr).strip().splitlines()
    return out[0] if out else '(no output)'


if __name__ == '__main__':
    runs = [
        ('baseline (Return/Constants.lean faces)', BASE_C, BASE_P, '3/50', None, None),
        ('numeratorCap 63/1000 alone', BASE_C, '49283557/50000000,4503/2000,63/1000', '63/1000', None,
         '993214/1000000,4503/2000,1/10'),
        ('hypothetical: physical capacity s_CS(0.8512), numeratorCap 3/50', BASE_C,
         '993214/1000000,4503/2000,31/500', '3/50', None, '993214/1000000,4503/2000,1/10'),
        ('hypothetical: physical capacity s_CS(0.8512), numeratorCap 63/1000', BASE_C,
         '993214/1000000,4503/2000,63/1000', '63/1000', None, '993214/1000000,4503/2000,1/10'),
    ]
    for name, cf, pf, nc, cs, ps in runs:
        print(f'{name:70s} {theta(cf, pf, nc, cs, ps)}')
