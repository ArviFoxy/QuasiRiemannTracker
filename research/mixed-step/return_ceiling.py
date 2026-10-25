import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'faceless-chain'))
from fractions import Fraction as Fr
import theta_eval as T
CAP = Fr(549989, 10**7)
cases = {
 'ours':        ((Fr('0.96775'), Fr('2.91120')), (Fr('0.97187'), Fr('3.00001'))),
 'P+0.009':     ((Fr('0.96775'), Fr('2.91120')), (Fr('0.98094'), Fr('3.00001'))),
 'C ideal':     ((Fr('0.99'), Fr('2.5')),        (Fr('0.97187'), Fr('3.00001'))),
 'perfect':     ((Fr('0.9999'), Fr('2.0')),      (Fr('0.9999'), Fr('3.00001'))),
 'both ideal':  ((Fr('0.99'), Fr('2.5')),        (Fr('0.99'), Fr('3.00001'))),
}
for k in sys.argv[1:]:
    (BC, LC), (BP, LP) = cases[k]
    print(k, T.theta_star((BC, LC, CAP), (BP, LP, CAP), lo=8700000), flush=True)
