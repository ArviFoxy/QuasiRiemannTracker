"""Run ../cap-induction/hybchain2.py with a different fee schedule (allowance e, lowFee r, highFee f).
usage: python3 hyb_fees.py e,r,f QF S1 STEP2 SEND OUT.json
PR #71 recosts Collet's graph under (1e-17, 1e-12, 1e-10), the fine accounting tuple permitted by
the accepted source theorem; our chains use (1e-12, 1e-8, 1e-7)."""
import sys, os, runpy
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
sys.path.insert(0, os.path.join(HERE, '..', 'cap-induction'))
import cchain_k as CK
CK.SCHED = tuple(float(x) for x in sys.argv[1].split(','))
print("fee schedule", CK.SCHED, flush=True)
sys.argv = [os.path.join(HERE, '..', 'cap-induction', 'hybchain2.py')] + sys.argv[2:]
runpy.run_path(sys.argv[0], run_name='__main__')
