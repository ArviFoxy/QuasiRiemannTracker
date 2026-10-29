"""Hypothetical plain fourth moment with slots at slot cost c_P and budget B = 1: the face G(1, c_P, cap) added
to today's region (merged faces kept).  Count face and physical face both read it.  Global check.
Usage: python3 plaincost.py <c_P> [cap]   [hypothetical input; numerical]"""
import sys
from globalcheck import theta_global
cP = float(sys.argv[1]); cap = float(sys.argv[2]) if len(sys.argv) > 2 else 0.12
t, where = theta_global((0.99999, cP, cap), (0.99999, cP))
print('plain slot cost c_P=%.3f cap=%.3f  global theta*=%.8f  %+.2e  binding %s d=%.2f p=%.2f %s'
      % ((cP, cap, t, t - 0.8738723399) + where), flush=True)
