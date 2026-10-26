"""Check that ret_new's general branch formulas reduce to FR4/FR6 at kL = 5/6, cI = 2."""
import os, sys
os.environ['QRH_FORCE_PATCH'] = '1'
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import importlib
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
import cert_return as CR0
orig_aff, orig_old = CR0.branch_affine, CR0.branch_old
import ret_new as RN
for (B, L) in [(Fr('0.9636'), Fr('2.09')), (Fr('0.97'), Fr('2.5'))]:
    for capped in (False, True):
        a = orig_aff(B, L, capped, Fr('0.058'))
        b = RN.branch_affine(B, L, capped, Fr('0.058'))
        for k in a:
            d = CR0.sub(a[k], b[k])
            assert not d, (k, capped, d)
for kap in (Fr('0.7485'), Fr('0.7')):
    a = orig_old(kap); b = RN.branch_old(kap)
    for k in ('J', 'N'):
        assert not CR0.sub(a[k], b[k]), k
print('branch formulas agree with FR4/FR6 exactly')
