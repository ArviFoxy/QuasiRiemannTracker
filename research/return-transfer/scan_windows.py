"""theta* of the return with the count windows opened (Lemma W): m_- = 0, affine and capped branches
of both faces at the face cap, capped C branch also at s_C, tail join at the width crossover.
usage: python3 scan_windows.py 'k=v,...' ...   (keys of base.DEF; extra key 'join' = collet|crossover,
'mminus' = lower plain window, 'zc' = extra capped widths for C separated by ':')"""
import sys
from fractions import Fraction as Fr
import base as B
import windows as W
CR = B.CR

def conf(P, zc_extra=()):
    capw = P['cap'] - Fr(1, 10**4)
    return {'C': dict(aff=[capw], cap=[P['sC'], capw] + list(zc_extra)),
            'P': dict(aff=[capw], cap=[P['sPp'], capw])}

def theta(spec):
    kv = dict(x.split('=') for x in spec.split(',') if x)
    W.JOIN = kv.pop('join', 'crossover')
    mm = Fr(kv.pop('mminus', '0'))
    zc = [Fr(z) for z in kv.pop('zc', '').split(':') if z]
    P = B.params(','.join(f'{k}={v}' for k, v in kv.items()))
    W.CONF = conf(P, zc)
    CR.M_MINUS = mm
    return B.theta_star(P, lo=8690000), P

if __name__ == '__main__':
    for a in sys.argv[1:]:
        t, _ = theta(a)
        print(a, t, flush=True)
