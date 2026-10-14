from model import *
from poly import bernstein
def q(v):
    v=Q(v); return f"{v.numerator}/{v.denominator}" if v.denominator!=1 else f"{v.numerator}"
def polystr(pol):
    terms=[]
    for (i,j) in sorted(pol.c):
        v=pol.c[(i,j)]
        mon=''.join([f"*δ^{i}" if i else "", f"*p^{j}" if j else ""])
        terms.append(f"({q(v)}){mon}")
    return " +\n  ".join(terms)
def box_lean(name, pol, boxes, m=2, n=3, extra_names=""):
    """boxes: list of (a,b,c,d). returns lean text"""
    allco=[]; cos=[]
    for bx in boxes:
        co=bernstein(pol,bx,m,n); cos.append(co); allco+= [x for r in co for x in r]
    mn=min(allco); assert mn>0,(name,float(mn))
    out=[]
    out.append(f"noncomputable def {name}Power (δ p : ℝ) : ℝ :=\n  {polystr(pol)}\n")
    out.append(f"noncomputable def {name}Minimum : ℝ := {q(mn)}\n")
    out.append(f"theorem {name}Minimum_pos : 0 < {name}Minimum := by\n  norm_num [{name}Minimum]\n")
    T="tensor" if (m,n)==(2,3) else "tensor24"
    b1,b2=("basis2","basis3") if (m,n)==(2,3) else ("basis2","basis4")
    for k,(bx,co) in enumerate(zip(boxes,cos)):
        a,b,c,d=bx
        rows=",\n    ".join("!["+", ".join(f"({q(x)} : ℝ)" for x in r)+"]" for r in co)
        out.append(f"noncomputable def {name}Coefficients{k} : Fin {m+1} → Fin {n+1} → ℝ :=\n  ![{rows}]\n")
        out.append(f"theorem {name}Coefficients{k}_lower (i : Fin {m+1}) (j : Fin {n+1}) :\n    {name}Minimum ≤ {name}Coefficients{k} i j := by\n  fin_cases i <;> fin_cases j <;> norm_num [{name}Minimum, {name}Coefficients{k}]\n")
        out.append(f"theorem {name}Identity{k} (δ p : ℝ) :\n    {name}Power δ p = {T} {name}Coefficients{k}\n      ((δ-({q(a)}))/(({q(b)})-({q(a)}))) ((p-({q(c)}))/(({q(d)})-({q(c)}))) := by\n  norm_num [{name}Power, {T}, {b1}, {b2},\n    {name}Coefficients{k}, Fin.sum_univ_succ]\n  ring\n")
        pos="tensor_pos" if (m,n)==(2,3) else "tensor24_pos"
        out.append(f"theorem {name}Box{k}_pos {{δ p : ℝ}}\n    (hδ : δ ∈ Set.Icc ({q(a)}) ({q(b)})) (hp : p ∈ Set.Icc ({q(c)}) ({q(d)})) :\n    0 < {name}Power δ p := by\n  rw [{name}Identity{k}]\n  exact {pos} {name}Minimum_pos\n    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)\n    {name}Coefficients{k}_lower\n")
    return "\n".join(out), mn
SIX=[(Q(0),Q(3,8),Q(0),Q(1,2)),(Q(3,8),Q(3,4),Q(0),Q(1,4)),(Q(3,8),Q(9,16),Q(1,4),Q(3,8)),(Q(3,8),Q(15,32),Q(3,8),Q(1,2)),(Q(15,32),Q(9,16),Q(3,8),Q(1,2)),(Q(9,16),Q(3,4),Q(1,4),Q(1,2))]
ra,rb,rc,rd=REG
COMP=[(Q(0),ra,Q(0),Q(1,2)),(rb,Q(3,4),Q(0),Q(1,2)),(ra,rb,Q(0),rc)]
REGB=[(ra,Q(93,200),rc,rd),(Q(93,200),Q(95,200),rc,rd),(Q(95,200),rb,rc,rd)]
import sys
blocks={}
blocks['newRow'],m1=box_lean('newRow', row_old(h,Q(1,10**6),True), COMP)
blocks['oldHalf'],m2=box_lean('oldHalf', row_old(Q(1,2),Q(1,1000),False), [(Q(0),Q(3,4),Q(0),Q(1,2))])
blocks['oldJunction'],m3=box_lean('oldJunction', row_old(dm,Q(1,10**5),False), SIX)
blocks['regionRow'],m4=box_lean('regionRow', row_new(h,Q(1,10**6),True), REGB)
for nm,pol in [('regionCrossLo',V1),('regionCrossHi',V2),('regionPlain',V3),('regionTail',V4),('regionCutoff',V5)]:
    blocks[nm],_=box_lean(nm,pol,[REG])
blocks['regionCompare'],_=box_lean('regionCompare',V6,[REG],2,4)
import pickle; pickle.dump(blocks,open('leanblocks.pkl','wb'))
for k,v in blocks.items(): print(k, len(v))
print('mins', float(m1), float(m2), float(m3), float(m4))
