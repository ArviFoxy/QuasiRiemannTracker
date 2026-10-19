/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCountArithmetic
import Candidate.Uneven.MainCountConcrete

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.MainCountArithmetic
open Target830
variable (P : MainCount.Plane)

theorem tN_formula (δ p : ℝ) :
    tN P δ p = Target830.Count.affineTNum P.lambda P.B δ p / Target830.Count.affineJ P.lambda δ p := by
  unfold tN numT JN DN aN cN Target830.Count.affineTNum Target830.Count.affineJ Target830.Count.affineU
    Target830.Count.affineD Target830.Count.affineA Target830.Count.affineC
  congr 1
  ring

theorem RNew_formula (δ p : ℝ) :
    RNew P δ p = Target830.Count.affineR P.lambda P.B δ p := by
  unfold RNew JN DN aN cN Target830.Count.affineR Target830.Count.affineJ Target830.Count.affineU
    Target830.Count.affineD Target830.Count.affineA Target830.Count.affineC
  ring

theorem crossing_mul (δ p : ℝ) (hD : DN P p ≠ 0)
    (hJ : Target830.Count.affineJ P.lambda δ p ≠ 0) :
    rN P p (tN P δ p) * (Target830.Count.affineD P.lambda p * Target830.Count.affineJ P.lambda δ p) =
      Target830.Count.affineRNum P.lambda P.B δ p := by
  have hr : rN P p (tN P δ p)*DN P p =
      aN P p*tN P δ p+2*p*P.B/P.lambda-p := div_mul_cancel₀ _ hD
  have ht : tN P δ p * Target830.Count.affineJ P.lambda δ p = Target830.Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula]
    exact div_mul_cancel₀ _ hJ
  change rN P p (tN P δ p)*(DN P p*Target830.Count.affineJ P.lambda δ p)=_
  calc
    _ = (aN P p*tN P δ p+2*p*P.B/P.lambda-p)*Target830.Count.affineJ P.lambda δ p := by rw [←hr];ring
    _ = aN P p*(tN P δ p*Target830.Count.affineJ P.lambda δ p)+
        (2*p*P.B/P.lambda-p)*Target830.Count.affineJ P.lambda δ p := by ring
    _ = _ := by rw [ht];rfl

theorem plain_mul (δ p : ℝ) (hD : DN P p ≠ 0)
    (hJ : Target830.Count.affineJ P.lambda δ p ≠ 0) :
    (tN P δ p-rN P p (tN P δ p)) *
      (Target830.Count.affineD P.lambda p*Target830.Count.affineJ P.lambda δ p) =
      Target830.Count.affineMNum P.lambda P.B δ p := by
  have hr := crossing_mul P δ p hD hJ
  have ht : tN P δ p*Target830.Count.affineJ P.lambda δ p=Target830.Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula];exact div_mul_cancel₀ _ hJ
  unfold Target830.Count.affineMNum
  linear_combination Target830.Count.affineD P.lambda p*ht-hr

/-- Every certified window supplies exactly the geometric and old-tail gates
of the actual affine detector count. -/
theorem admissible_geometry {δ p κ : ℝ} (h : MainCount.Admissible P δ p)
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hk : 7/10 ≤ κ) (hkhi : κ ≤ kappa0) :
    1 ≤ tN P δ p ∧ tN P δ p ≤ 3/2 ∧
      23/37 ≤ rN P p (tN P δ p) ∧ rN P p (tN P δ p) ≤ 1 ∧
      MainCount.lowerPlain P+1/100000 ≤ tN P δ p-rN P p (tN P δ p) ∧
      MainCountArithmetic.oldPlainExp δ p κ MainCount.mHi ≤ shortNew P δ p (tN P δ p) := by
  have hD : 0 < Target830.Count.affineD P.lambda p := h.denominator
  have hJ : 0 < Target830.Count.affineJ P.lambda δ p := h.j
  have hD' : DN P p ≠ 0 := hD.ne'
  have hprod : 0 < Target830.Count.affineD P.lambda p*Target830.Count.affineJ P.lambda δ p := mul_pos hD hJ
  have ht : tN P δ p*Target830.Count.affineJ P.lambda δ p=Target830.Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula];exact div_mul_cancel₀ _ hJ.ne'
  have hr := crossing_mul P δ p hD' hJ.ne'
  have hm := plain_mul P δ p hD' hJ.ne'
  have htlo := h.cutoff_lower
  have hthi := h.cutoff_upper
  have hrlo := h.cross_lower
  have hrhi := h.cross_upper
  have hmlo := h.plain_lower
  simp only [MainCount.guardTLo,MainCount.guardTHi] at htlo hthi
  simp only [MainCount.guardRLo,MainCount.guardRHi] at hrlo hrhi
  unfold MainCount.guardMLo at hmlo
  have ht0 : 1 ≤ tN P δ p := by nlinarith only [ht,htlo,hJ]
  have ht1 : tN P δ p ≤ 3/2 := by nlinarith only [ht,hthi,hJ]
  have hr0 : 23/37 ≤ rN P p (tN P δ p) := by nlinarith only [hr,hrlo,hprod]
  have hr1 : rN P p (tN P δ p) ≤ 1 := by nlinarith only [hr,hrhi,hprod]
  rw [mul_assoc] at hmlo
  change 0 < Target830.Count.affineMNum P.lambda P.B δ p -
    max plainLower (MainCount.lowerPlain P+1/100000)*(Target830.Count.affineD P.lambda p*Target830.Count.affineJ P.lambda δ p) at hmlo
  have hhmax := le_max_right plainLower (MainCount.lowerPlain P+1/100000)
  have hhmax' := mul_le_mul_of_nonneg_right hhmax hprod.le
  have hm0 : MainCount.lowerPlain P+1/100000 ≤ tN P δ p-rN P p (tN P δ p) := by
    nlinarith only [hm,hmlo,hhmax',hprod]
  refine ⟨ht0,ht1,hr0,hr1,hm0,?_⟩
  have hR : RNew P δ p*Target830.Count.affineJ P.lambda δ p=Target830.Count.affineN P.lambda P.B δ p := by
    rw [RNew_formula]
    exact Target830.Count.affine_count_mul hJ.ne'
  have htail := h.tail
  unfold MainCount.guardTail at htail
  have hbound : 1-2*δ*MainCount.mHi-2*δ*p*widthLower ≤ RNew P δ p := by
    nlinarith only [htail,hR,hJ]
  have hk0 : 0 < 6*κ := by linarith
  have hcap : widthLower ≤ (1-2*MainCount.mHi)/(6*κ) := by
    rw [le_div_iff₀ hk0]
    have hid : 1-2*MainCount.mHi=6*kappa0*widthLower := by unfold MainCount.mHi Target830.Count.mHi;ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_right hkhi (show (0:ℝ) ≤ 6*widthLower by norm_num [widthLower])
    nlinarith only [hh]
  have hstep : oldPlainExp δ p κ MainCount.mHi ≤ 1-2*δ*MainCount.mHi-2*δ*p*widthLower := by
    have hh := mul_le_mul_of_nonneg_left hcap (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hδ) hp)
    unfold oldPlainExp
    calc
      _ = 1-2*δ*MainCount.mHi-(2*δ*p*((1-2*MainCount.mHi)/(6*κ))) := by ring
      _ ≤ _ := sub_le_sub_left hh _
  have hmax := short_at_tN P (show JN P δ p ≠ 0 from hJ.ne') hD'
  rw [hmax]
  exact hstep.trans hbound

end OAI.SevenEighths.MainCountArithmetic
end
#print axioms OAI.SevenEighths.MainCountArithmetic.admissible_geometry
