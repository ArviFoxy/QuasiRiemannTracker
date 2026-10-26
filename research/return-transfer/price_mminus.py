"""Price the count's lower plain window m_- (FR3/FR8: m_L = m_- + eta for capped branches,
max(m_- + eta, (B - L(s_+ - eta))/2 + eta) for affine ones).  Collet fixes m_- = 2/5; the count's
moment is the broad face [0, 1/2] x [0, cap] (Lean: count_from_piecewise_moments needs only 0 <= mLo).
usage: python3 price_mminus.py m1 m2 ... [--spec 'k=v,...']"""
import sys
from fractions import Fraction as Fr
import base as B
CR = B.CR

def main():
    args = sys.argv[1:]
    spec = ''
    if '--spec' in args:
        i = args.index('--spec'); spec = args[i+1]; args = args[:i] + args[i+2:]
    P = B.params(spec)
    for a in args:
        CR.M_MINUS = Fr(a)
        t = B.theta_star(P, lo=8690000)
        print(f"m_- = {a}: theta* = {t}", flush=True)

if __name__ == '__main__':
    main()
