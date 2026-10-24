from fractions import Fraction as Fr
import cert_return as CR
theta = Fr(8747729897, 10**10); h = Fr(8001009617, 10**10)
C = (Fr('0.96226151753982'), Fr('3.14813176381578'), Fr('0.0549989'))
P = (Fr('0.96739031091242'), Fr('3.27307995389766'), Fr('0.0549989'))
G = CR.geometry(theta, h, P[0], P[1])
rec = CR.receipt(G, P[0], P[1], C[2], P[2], Fr(11,250), Fr(43,1000), Fr(8747759,10**7))
ref = {'Gram_x_above_ell': Fr(1998990383,10**10), 'Gram_y_above_x': Fr(487388999,5*10**9),
 'conductor_top_before_twoy': Fr(121689497,937500000), 'physical_plain_lower': Fr(1256797809,125*10**9),
 'physical_plain_upper': Fr(2234201241610573,120015144270000000), 'physical_width_upper': Fr(29999,10**7),
 'small_width_shortening': Fr(507914723825573,120015144270000000), 'short_plain_shortening': Fr(2207929527179,125*10**13),
 'large_shift': Fr(196059842393,375*10**13), 'large_shift_clipped': Fr(28249845426025867,81826998847441500),
 'prime_supply': Fr(566588663,60007572135), 'capacity_domain': Fr(121689497,1875000000), 'incumbent': Fr(29103,5*10**9),
 'feedback_kappa': Fr(247729897,5*10**9), 'floor': Fr(4258073897,10**12), 'small_row': Fr(56237409433,15*10**11),
 'principal_w': Fr(635924290099,3*10**13), 'principal_z': Fr(501009617,6*10**12), 'holomorphic_box': Fr(247729897,10**10),
 'source_intercept': Fr(1630484454379,5*10**13), 'physical_width_lower': Fr(80034821928134267062407482959,19640958143713630685770410000000)}
for k,v in ref.items():
    print(f"{k:28s} mine={float(rec[k]):.12e} ref={float(v):.12e} {'OK' if rec[k]==v else 'DIFF'}")
rec2, cov, bad = CR.run(theta, h, C, P)
print("rectangles", len(cov))
