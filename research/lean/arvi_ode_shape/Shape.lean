/-
The continuous energy region estimate: every face of the explicit curve is proven, by one induction.

`curve_step`: one density step along the curve, from the face at `Λ₀` to the face at `Λ ∈ [Λ₀ - hmax, Λ₀)`
(`Density.density_step_marked` with the gates of `Gates.lean` and `HighStep.lean`).
`ode_shape_sources`: every face `(β Λ, Λ, 1/10)`, `Λ ∈ [La, Lb]`, from the top face, by `curve_induction`.
No face is listed; the curve is the seven coefficients of `Curve.lean`.
-/
import Submissions.arvi_ode_shape.HighStep
import Submissions.arvi_ode_shape.Induction
import Submissions.arvi_energy_region.EnergyRegion

set_option autoImplicit false

namespace QRH.ArviOdeShape
open QRH.ArviReturnTuning QRH.ArviDensity QRH.ArviDensity.Hybrid QRH.ArviUniformChain Set
open OAI OAI.SevenEighths

/-- **Containment of global faces** (an LP over the smaller face): `(B', Λ', c')` lies inside `(B, Λ, c)` when
`c' ≤ c`, `B' ≤ B` and `B' + (Λ - Λ') c' ≤ B` (the second face's line stays below the first at `s = 0` and at
`s = c'`). -/
theorem globalFace_subset {B Λ c B' Λ' c' : ℝ} (hc : c' ≤ c) (hc0 : 0 ≤ c') (hB : B' ≤ B)
    (hB' : B' + (Λ - Λ') * c' ≤ B) (hBpos : 0 < B') :
    QRH.ArviEnergyRegion.faceRegion (QRH.Record1252270103Source.globalFace B' Λ' c') ⊆
      QRH.ArviEnergyRegion.faceRegion (QRH.Record1252270103Source.globalFace B Λ c) := by
  rintro ⟨m₁, m₂, s, M⟩ hx
  simp only [QRH.ArviEnergyRegion.faceRegion, QRH.Record1252270103Source.globalFace,
    QRH.Record12518109Source.SourceFace.Admissible, Set.mem_ofPred_eq] at hx ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hx
  have h5' : 0 ≤ s := by simpa using h5
  have hM : 0 ≤ M := by
    by_contra hneg
    have : M < 0 := lt_of_not_ge hneg
    nlinarith
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hB hM), h3, h4.trans (mul_le_mul_of_nonneg_right hB hM),
    h5, h6.trans (mul_le_mul_of_nonneg_right hc hM), ?_⟩
  -- m₁ + m₂ + Λ s = (m₁ + m₂ + Λ' s) + (Λ - Λ') s ≤ B' M + max(0, Λ - Λ') c' M ≤ B M
  rcases le_total Λ' Λ with hΛ | hΛ
  · have : (Λ - Λ') * s ≤ (Λ - Λ') * (c' * M) := mul_le_mul_of_nonneg_left h6 (by linarith)
    nlinarith
  · have : (Λ - Λ') * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h5'
    nlinarith

theorem globalSource_mono {B Λ c B' Λ' c' : ℝ} (hc : c' ≤ c) (hc0 : 0 ≤ c') (hB : B' ≤ B)
    (hB' : B' + (Λ - Λ') * c' ≤ B) (hBpos : 0 < B')
    (h : QRH.Record1252270103Source.GlobalSource B Λ c) : QRH.Record1252270103Source.GlobalSource B' Λ' c' :=
  (QRH.ArviEnergyRegion.isEstimate_globalFace_iff B' Λ' c').mp
    (((QRH.ArviEnergyRegion.isEstimate_globalFace_iff B Λ c).mpr h).mono
      (globalFace_subset hc hc0 hB hB' hBpos))

/-- The parent `t` of a curve point. -/
noncomputable def tOf (Λ : ℝ) : ℝ := (Λ - Lm) / Lh

theorem Lr_tOf (Λ : ℝ) : Lr (tOf Λ) = Λ := by
  simp only [Lr, tOf]; field_simp [Lh_pos.ne']; ring

theorem tOf_mem {Λ : ℝ} (hΛ : Λ ∈ Icc (La : ℝ) Lb) : tOf Λ ∈ Icc (-1 : ℝ) 1 := by
  have h1 := hΛ.1; have h2 := hΛ.2
  simp only [tOf, La, Lb, Lm, Lh] at h1 h2 ⊢; push_cast at h1 h2 ⊢
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [div_le_iff₀ (by norm_num)]; linarith

/-- **One density step along the curve**, given the facet input of the step. -/
theorem curve_step {Λ₀ Λ : ℝ} (hΛ₀ : Λ₀ ∈ Icc (La : ℝ) Lb) (hΛ : Λ ∈ Icc (La : ℝ) Lb) (hlt : Λ < Λ₀)
    (hle : Λ₀ - Λ ≤ hmax) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hfac : FacetInput Λ₀ (beta Λ₀) (Sr (tOf Λ₀) (Λ₀ - Λ)) (Λ₀ - Λ))
    (hsrc : QRH.Record1252270103Source.GlobalSource (beta Λ₀) Λ₀ (1/10)) :
    QRH.Record1252270103Source.GlobalSource (beta Λ) Λ (1/10) := by
  set t := tOf Λ₀
  set h := Λ₀ - Λ
  have ht := tOf_mem hΛ₀
  have hh : 0 < h := sub_pos.mpr hlt
  have hL : Lr t = Λ₀ := Lr_tOf Λ₀
  have hB : Br t = beta Λ₀ := by simp only [Br, hL]
  have S := stepFacts ht hh hle
  rw [hL, hB] at S
  have hchild : beta Λ₀ - Sr t h * h = beta Λ := by
    have := child_eq t h; rw [hL] at this; rw [← hB, this]; congr 1; ring
  have hLchild : Λ₀ - h = Λ := by ring
  -- the HIGH gate
  have hhigh : HighCurve t h := by
    obtain ⟨r, hr, hall⟩ := high_of_stepFacts S hfac
    refine ⟨r, hr, ?_⟩
    intro v hv0 hv1 ν hν0 hν1
    have hcr := cross_curve t h hh.ne'
    rw [hcr] at hv1
    have hw : width (Br t) (Lr t) (Br t - Sr t h * h) (Lr t - h) v = Sr t h + v := by
      unfold width; rw [hcr]
    rw [hw]
    have hd : dens (Br t) (Lr t) (Lr t - h) (19/50) 100 v = qd Λ₀ (beta Λ₀) h v := by
      simp only [qd, hL, hB]
    rw [hd] at hν0
    rw [hL, hB]
    exact hall v hv0 hv1 ν hν0 hν1
  have G := hybridGatesM_curve ht hh hle hhigh
  rw [hL, hB, hchild, hLchild] at G
  have hBlo : 22/23 ≤ beta Λ₀ := S.B_lo.le
  have hF : Density.DSFace (beta Λ₀) Λ₀ (1/10) (beta Λ) Λ (1/10) := by
    refine ⟨?_, S.B_hi, hlt, by linarith [hΛ.1, show (1:ℝ) < La by norm_num [La]], by norm_num, by norm_num⟩
    rw [← hchild]
    have : 0 ≤ Sr t h * h := mul_nonneg (by linarith [S.s_lo]) hh.le
    linarith
  exact Density.density_step_marked (1/2) (beta Λ₀) Λ₀ (1/10) (beta Λ) Λ (1/10) (19/50) 100
    (by norm_num) (by norm_num) hBlo G hF hβ hsrc

/-- **The continuous energy region estimate.** From the top face, every face `(β Λ, Λ, 1/10)` of the curve,
`Λ ∈ [La, Lb]`, is proven. The facet input is required for every step of the curve. -/
theorem ode_shape_sources (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hfac : ∀ Λ₀ ∈ Icc (La : ℝ) Lb, ∀ Λ ∈ Icc (La : ℝ) Lb, Λ < Λ₀ → Λ₀ - Λ ≤ hmax →
      FacetInput Λ₀ (beta Λ₀) (Sr (tOf Λ₀) (Λ₀ - Λ)) (Λ₀ - Λ))
    (htop : QRH.Record1252270103Source.GlobalSource (beta Lb) Lb (1/10)) :
    ∀ Λ ∈ Icc (La : ℝ) Lb, QRH.Record1252270103Source.GlobalSource (beta Λ) Λ (1/10) :=
  curve_induction (fun Λ => QRH.Record1252270103Source.GlobalSource (beta Λ) Λ (1/10))
    (by norm_num [hmax]) htop
    (fun Λ₀ hΛ₀ Λ hΛ hlt hle hsrc => curve_step hΛ₀ hΛ hlt hle hβ (hfac Λ₀ hΛ₀ Λ hΛ hlt hle) hsrc)

end QRH.ArviOdeShape

#print axioms QRH.ArviOdeShape.ode_shape_sources
