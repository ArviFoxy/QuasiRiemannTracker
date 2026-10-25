"""Does the return floor (perfect source faces) move with the return's design parameters?"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import atlas as A
A.init()
perfect = dict(A.BASE, BC=Fr('0.9999'), LC=Fr('2.0'), BP=Fr('0.9999'), LP=Fr('3.00001'))
if os.environ.get('CAP'): A.CAP = Fr(os.environ['CAP'])
for kv in sys.argv[1:]:
    P = dict(perfect)
    for item in kv.split(','):
        k, v = item.split('=')
        P[k] = Fr(v)
    print(kv, A.theta_star(P, guess=8745804), flush=True)
