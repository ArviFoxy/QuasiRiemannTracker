"""ODE model at floor 1/2: sensitivity of theta to the repeated-mark copy count K (Lean: K = 8) and the parent cap h0."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ta'))
import run_ode2
run_ode2.RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
os.makedirs(run_ode2.RES, exist_ok=True)
K = int(sys.argv[1]); h0 = float(sys.argv[2])
run_ode2.run_ode(1.0, False, 0.999, [0.50], tag='_K%d_h%g' % (K, h0), K=K, h0=h0)
