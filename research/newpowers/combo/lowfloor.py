"""ODE model: floors below 1/2 (what-if: the zero-density count holds for a > 51/100, see Collet's
actual_maxima_bin_count; the q > 1/2 gate of PR 83 is assumed removable).  B >= 22/23 still gates the marked gain."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ta'))
import numpy as np
import ode2, run_ode2
run_ode2.RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
os.makedirs(run_ode2.RES, exist_ok=True)


def _dead(self, L, y):
    return self.q(y[0], L) - 0.25
_dead.terminal = True
ode2.Chain2._dead = _dead
Lend = float(sys.argv[2]) if len(sys.argv) > 2 else 1.5
floors = [float(x) for x in sys.argv[1].split(',')]
run_ode2.run_ode(1.0, False, 0.999, floors, tag='_low', Lend=Lend)
