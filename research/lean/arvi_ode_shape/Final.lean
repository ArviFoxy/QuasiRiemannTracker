/-
The merged bound from the continuous energy region estimate, without the 129-step density chain.

The chain of sources is: PR 76's fourth-power source; the native line (`NativeCurve.lean`); the density curve
(`Shape.lean`); the return. The return of PR #94 reads two faces: the count face `G(96232839/10⁸, 3853/2000, 1/10)` and the physical face
`G(49283557/(5·10⁷), 4503/2000, 1/10)`. Both lie inside faces of the curve (`globalSource_mono`): the curve's end
`(β La, La)` and its point at `Λ = 4503/2000`. The top face of the curve lies inside the end of the native line.
-/
import Submissions.arvi_ode_shape.Shape
import Submissions.arvi_return_tuning.Endpoint
import Submissions.arvi_ode_shape.NativeCurve

set_option autoImplicit false

namespace QRH.ArviOdeShape
open QRH.ArviReturnTuning Set
open OAI OAI.SevenEighths

theorem beta_Lb : beta Lb = 999989894999/1000000000000 := by
  simp only [beta, curveQ, Lb, Lm, Lh, Q1.ev_cons, Q1.ev_nil]; norm_num

theorem beta_La : beta La = 962486277089/1000000000000 := by
  simp only [beta, curveQ, La, Lm, Lh, Q1.ev_cons, Q1.ev_nil]; norm_num

theorem beta_P : 49283557/50000000 + 1/50000 ≤ beta (4503/2000) := by
  simp only [beta, curveQ, Lm, Lh, Q1.ev_cons, Q1.ev_nil]; norm_num

/-- The top face of the curve, inside the end `G(99999/100000, 5143/2000, 1/10)` of the native line. -/
theorem top_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (beta Lb) Lb (1/10) := by
  have hend := native_end hβ
  have hLb : ((Lb : ℚ) : ℝ) = 5143/2000 := by norm_num [Lb]
  rw [beta_Lb, hLb]
  exact globalSource_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hend

/-- The facet input along the whole curve (supplied by `FacetForms`). -/
def FacetsAll : Prop :=
  ∀ Λ₀ ∈ Icc (La : ℝ) Lb, ∀ Λ ∈ Icc (La : ℝ) Lb, Λ < Λ₀ → Λ₀ - Λ ≤ hmax →
    FacetInput Λ₀ (beta Λ₀) (Sr (tOf Λ₀) (Λ₀ - Λ)) (Λ₀ - Λ)

theorem curve_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (hfac : FacetsAll) {Λ : ℝ}
    (hΛ : Λ ∈ Icc (La : ℝ) Lb) : QRH.Record1252270103Source.GlobalSource (beta Λ) Λ (1/10) :=
  ode_shape_sources hβ hfac (top_source hβ) Λ hΛ

/-- The return's count face, inside the curve's end face. -/
theorem count_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (hfac : FacetsAll) :
    QRH.Record1252270103Source.GlobalSource (96232839/100000000) (3853/2000) (1/10) := by
  have h := curve_source hβ hfac (Λ := La) ⟨le_rfl, by norm_num [La, Lb]⟩
  rw [beta_La] at h
  have hLa : ((La : ℚ) : ℝ) = 4819/2500 := by norm_num [La]
  rw [hLa] at h
  exact globalSource_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

/-- The return's physical face, inside the curve's face at `Λ = 4503/2000`. -/
theorem physical_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (hfac : FacetsAll) :
    QRH.Record1252270103Source.GlobalSource (49283557/50000000) (4503/2000) (1/10) := by
  have h := curve_source hβ hfac (Λ := 4503/2000) ⟨by norm_num [La], by norm_num [Lb]⟩
  have hP := beta_P
  exact globalSource_mono (by norm_num) (by norm_num) (by linarith) (by linarith) (by norm_num) h

/-- **The merged bound without the density chain**: `β ≤ 43693617/50000000` from the continuous energy region
estimate (the curve) and the merged return. -/
theorem beta_le_theta_of_curve (hfac : FacetsAll) :
    HeckeZeroSupremum.beta ≤ (43693617/50000000 : ℝ) :=
  QRH.ArviDensity.Return.Tuning.beta_le_theta_of_sources (fun hβ => count_source hβ hfac)
    (fun hβ => physical_source hβ hfac)

theorem dirichlet_of_curve (hfac : FacetsAll) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (43693617 / 50000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.ArviDensity.Return.Tuning.dirichlet_of_sources (fun hβ => count_source hβ hfac)
    (fun hβ => physical_source hβ hfac) χ hs hpole

end QRH.ArviOdeShape

#print axioms QRH.ArviOdeShape.top_source
#print axioms QRH.ArviOdeShape.beta_le_theta_of_curve
#print axioms QRH.ArviOdeShape.dirichlet_of_curve
