/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Full numerical row intervals, conditional only on the stated count bounds. -/
import Candidate.Uneven.RoundedAllRows
import Candidate.Uneven.RowInterpolation

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

def rowConstant (d p : ℝ) : ℝ :=
  (1+d)/2+13*h/75-y/2-ell/2+ell*d*p

def scalarRow (z cap count d p : ℝ) : ℝ :=
  rowConstant d p-9*z/100-d*p*cap/2+3*z*count/4

def oldCapacity (z : ℝ) : ℝ := min z (2*y-z)/(6*frozen_kappa)
def newCapacity (z : ℝ) : ℝ :=
  min ((399999/10000000)*z)
    ((2*y-(2-Critical.physicalB)*z)/Critical.physicalLambda)

def CountBounds (count d p : ℝ) : Prop :=
  ∀ i : ℕ, i ≤ 7 → available i d p → count ≤ numerator i d p/denominator i d p

theorem scalar_row_eq (r i : ℕ) (d p : ℝ) :
    scalarRow (rowHeight r) (rowCapacity r)
      (numerator i d p/denominator i d p) d p = row r i d p := by
  unfold scalarRow rowConstant row base
  ring

theorem scalar_row_mono {z cap count count' d p : ℝ}
    (hz : 0 ≤ z) (hc : count ≤ count') :
    scalarRow z cap count d p ≤ scalarRow z cap count' d p := by
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*z/4 by positivity)
  unfold scalarRow
  nlinarith only [hh]

theorem scalar_endpoints {r : ℕ} (hr : r ≤ 3) {d p count : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hc : CountBounds count d p) :
    scalarRow (rowHeight r) (rowCapacity r) count d p ≤ theta-1/20000000000000 := by
  obtain ⟨i,hi,ha,hb⟩ := full_rows hr hd hp
  have hz : 0 ≤ rowHeight r := by interval_cases r <;> norm_num [rowHeight]
  have hm := scalar_row_mono (cap:=rowCapacity r) (d:=d) (p:=p) hz (hc i hi ha)
  rw [scalar_row_eq] at hm
  exact hm.trans hb

theorem old_row_formula (z count d p : ℝ) :
    scalarRow z (oldCapacity z) count d p =
      rowConstant d p+(-9/100+3*count/4)*z-
        (d*p/(12*frozen_kappa))*min (0+1*z) (2*y+(-1)*z) := by
  unfold scalarRow oldCapacity
  norm_num [frozen_kappa]
  ring

theorem new_row_formula (z count d p : ℝ) :
    scalarRow z (newCapacity z) count d p =
      rowConstant d p+(-9/100+3*count/4)*z-
        (d*p/2)*min (0+(399999/10000000)*z)
          (2*y/Critical.physicalLambda+(-(2-Critical.physicalB)/Critical.physicalLambda)*z) := by
  have he : (2*y-(2-Critical.physicalB)*z)/Critical.physicalLambda =
      2*y/Critical.physicalLambda+(-(2-Critical.physicalB)/Critical.physicalLambda)*z := by ring
  unfold scalarRow newCapacity
  rw [he]
  simp only [zero_add]
  ring

theorem old_row_interval {z count d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1)
    (hc : CountBounds count d p) :
    scalarRow z (oldCapacity z) count d p ≤ theta-1/20000000000000 := by
  have h0 := scalar_endpoints (r:=0) (by norm_num) hd hp hc
  have h1 := scalar_endpoints (r:=1) (by norm_num) hd hp hc
  have he0 : rowCapacity 0=oldCapacity (rowHeight 0) := by
    simpa only [actualCapacity,oldCapacity,show (0:ℕ) ≤ 1 by norm_num,if_pos] using
      row_capacity_eq_actual (r:=0) (by norm_num)
  have he1 : rowCapacity 1=oldCapacity (rowHeight 1) := by
    simpa only [actualCapacity,oldCapacity,show (1:ℕ) ≤ 1 by norm_num,if_pos] using
      row_capacity_eq_actual (r:=1) (by norm_num)
  rw [he0,old_row_formula] at h0
  rw [he1,old_row_formula] at h1
  rw [old_row_formula]
  apply RowInterpolation.min_capacity_between _ _ _ _ _ _ _ _ _ _ _ _ hz h0 h1
  exact div_nonneg (mul_nonneg hd.1 hp.1) (by norm_num [frozen_kappa])

theorem new_row_interval {z count d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3)
    (hc : CountBounds count d p) :
    scalarRow z (newCapacity z) count d p ≤ theta-1/20000000000000 := by
  have h0 := scalar_endpoints (r:=2) (by norm_num) hd hp hc
  have h1 := scalar_endpoints (r:=3) (by norm_num) hd hp hc
  have he0 : rowCapacity 2=newCapacity (rowHeight 2) := by
    simpa only [actualCapacity,newCapacity,show ¬ (2:ℕ) ≤ 1 by norm_num,ite_false] using
      row_capacity_eq_actual (r:=2) (by norm_num)
  have he1 : rowCapacity 3=newCapacity (rowHeight 3) := by
    simpa only [actualCapacity,newCapacity,show ¬ (3:ℕ) ≤ 1 by norm_num,ite_false] using
      row_capacity_eq_actual (r:=3) (by norm_num)
  rw [he0,new_row_formula] at h0
  rw [he1,new_row_formula] at h1
  rw [new_row_formula]
  apply RowInterpolation.min_capacity_between _ _ _ _ _ _ _ _ _ _ _ _ hz h0 h1
  exact div_nonneg (mul_nonneg hd.1 hp.1) (by norm_num)

end Sil.Uneven.RoundedRows
#print axioms Sil.Uneven.RoundedRows.old_row_interval
#print axioms Sil.Uneven.RoundedRows.new_row_interval
