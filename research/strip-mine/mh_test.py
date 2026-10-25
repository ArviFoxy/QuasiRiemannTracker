"""Tail join M_H from Sil's face instead of the natural face (hypothetical): theta* with our faces."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import atlas as A, knobs as KB
A.init()
orig = KB.apply_module_knobs
def with_mh(value):
    def f(mod):
        orig(mod); mod.M_H = value
    return f
for label, mh in [('natural (1-9/2*17/500)/2', None),
                  ('Sil (0.99999-93/25*17/500)/2', (Fr(99999, 100000) - Fr(93, 25)*Fr(17, 500))/2)]:
    KB.apply_module_knobs = orig if mh is None else with_mh(mh)
    A.KB.apply_module_knobs = KB.apply_module_knobs
    print(label, float(mh) if mh else '', A.theta_star(dict(A.BASE)), flush=True)
