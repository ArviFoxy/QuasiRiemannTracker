import Candidate.Target830.Kernel.BalancedGeometry
import Candidate.Uneven.SkewCone

/- Copyright (c) 2026 Sil. Apache-2.0.
   Extends PR63's balanced source geometry; inherited declarations are unchanged.
   Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
namespace Sil.Uneven.Geometry
noncomputable section
open QRH830.BalancedGeometry

def left (a c d r e p : ℝ) : ℝ :=
  QRH830.BalancedGeometry.left a c d r e + SkewNormalization.skew c d r p

def right (a c d r e p : ℝ) : ℝ :=
  QRH830.BalancedGeometry.right a c d r e - SkewNormalization.skew c d r p

theorem surplus_eq (c d r p : ℝ) :
    surplus c d r p = SkewNormalization.surplus c d r p := rfl

theorem left_normalization (a c d r e p : ℝ) :
    oldLeft a c d r e p +
      (surplus c d r p + SkewNormalization.skew c d r p) = left a c d r e p := by
  unfold left
  linarith only [QRH830.BalancedGeometry.left_normalization a c d r e p]

theorem right_normalization (a c d r e p : ℝ) :
    oldRight a c d r e p +
      (surplus c d r p - SkewNormalization.skew c d r p) = right a c d r e p := by
  unfold right
  linarith only [QRH830.BalancedGeometry.right_normalization a c d r e p]

theorem allocations_nonnegative {c d r p : ℝ} (hs : 0 ≤ surplus c d r p) :
    0 ≤ surplus c d r p + SkewNormalization.skew c d r p ∧
    0 ≤ surplus c d r p - SkewNormalization.skew c d r p := by
  exact SkewNormalization.allocations_nonnegative (r := (d-c)/10) hs

theorem budget (m a c d r e p : ℝ) :
    outer m a r e + (left a c d r e p + right a c d r e p)/2 = m := by
  unfold left right
  linarith only [QRH830.BalancedGeometry.balanced_budget m a c d r e]

theorem reflection {a c d r e p : ℝ} (hs : 0 ≤ surplus c d r p) :
    left a d c r e p = right a c d r e p := by
  have h := SkewNormalization.skew_reflect c d r p hs
  unfold left right QRH830.BalancedGeometry.left QRH830.BalancedGeometry.right
  rw [h]
  ring

theorem right_bin_bound {a c d r e p c' d' r' e' p' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w)
    (hr : |r'-r| ≤ w) (he : |e'-e| ≤ w) (hp : |p'-p| ≤ w) :
    |right a c' d' r' e' p' - right a c d r e p| ≤ 41*w/5 := by
  have hb := QRH830.BalancedGeometry.right_bin_bound (a := a) hc hd hr he
  have ht := SkewNormalization.skew_lipschitz hc hd hr hp
  rcases abs_le.mp hb with ⟨hb0, hb1⟩
  rcases abs_le.mp ht with ⟨ht0, ht1⟩
  rw [abs_le]
  unfold right
  constructor <;> linarith only [hb0, hb1, ht0, ht1]

theorem cross_label_budget {m a c d r e p c' d' r' e' p' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w)
    (hr : |r'-r| ≤ w) (he : |e'-e| ≤ w) (hp : |p'-p| ≤ w) :
    outer m a r e + (left a c d r e p + right a c' d' r' e' p')/2 ≤
      m + 41*w/10 := by
  have hb := (abs_le.mp (right_bin_bound (a := a) hc hd hr he hp)).2
  have h := budget m a c d r e p
  linarith only [hb, h]

end
end Sil.Uneven.Geometry

#print axioms Sil.Uneven.Geometry.allocations_nonnegative
#print axioms Sil.Uneven.Geometry.budget
#print axioms Sil.Uneven.Geometry.reflection
#print axioms Sil.Uneven.Geometry.cross_label_budget
