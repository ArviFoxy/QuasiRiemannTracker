/-
The ODE-inequality energy region estimate: the faces of a curve, proven by one induction.

A curve Λ ↦ (β Λ, Λ) whose slope β' is antitone (β concave) has every chord slope between the derivatives at
its ends (mean value theorem). If one density step is valid for every face of the curve, every chord slope in
that window and every step length up to `h₀` (the generator lemma, the hypothesis `hgood`), then every face of
the curve is proven, by continuous induction over the interval. No face is listed.
-/
import Submissions.arvi_density.Density.StepMarked

set_option autoImplicit false

namespace QRH.ArviOdeShape
noncomputable section

open Set

/-- **Continuous induction.** A property that holds at the top `Λb` and passes from any point to every point at
most `h₀` below it holds on all of `[Λa, Λb]`. -/
theorem curve_induction (P : ℝ → Prop) {Λa Λb h₀ : ℝ} (hh₀ : 0 < h₀) (htop : P Λb)
    (hstep : ∀ Λ₀ ∈ Icc Λa Λb, ∀ Λ ∈ Icc Λa Λb, Λ < Λ₀ → Λ₀ - Λ ≤ h₀ → P Λ₀ → P Λ) :
    ∀ Λ ∈ Icc Λa Λb, P Λ := by
  have key : ∀ n : ℕ, ∀ Λ ∈ Icc Λa Λb, Λb - n * h₀ ≤ Λ → P Λ := by
    intro n
    induction n with
    | zero =>
      intro Λ hΛ h
      have : Λ = Λb := le_antisymm hΛ.2 (by simpa using h)
      exact this ▸ htop
    | succ n ih =>
      intro Λ hΛ h
      by_cases hc : Λb - n * h₀ ≤ Λ
      · exact ih Λ hΛ hc
      · have hc' : Λ < Λb - n * h₀ := lt_of_not_ge hc
        have hn : (0:ℝ) ≤ n * h₀ := mul_nonneg (Nat.cast_nonneg n) hh₀.le
        have hcast : ((n + 1 : ℕ) : ℝ) * h₀ = n * h₀ + h₀ := by push_cast; ring
        rw [hcast] at h
        set Λ₀ := min (Λ + h₀) Λb with hΛ₀def
        have hΛ₀a : Λa ≤ Λ₀ := le_min (by linarith [hΛ.1]) (hΛ.1.trans hΛ.2)
        have hΛ₀ : Λ₀ ∈ Icc Λa Λb := ⟨hΛ₀a, min_le_right _ _⟩
        have h1 : Λb - n * h₀ ≤ Λ₀ := le_min (by linarith) (by linarith)
        have hlt : Λ < Λ₀ := lt_min (by linarith) (by linarith)
        have hle : Λ₀ - Λ ≤ h₀ := by linarith [min_le_left (Λ + h₀) Λb]
        exact hstep Λ₀ hΛ₀ Λ hΛ hlt hle (ih Λ₀ hΛ₀ h1)
  intro Λ hΛ
  obtain ⟨n, hn⟩ := exists_nat_ge ((Λb - Λ) / h₀)
  refine key n Λ hΛ ?_
  have := (div_le_iff₀ hh₀).mp hn
  linarith

/-- Chord slopes of a curve with antitone slope lie between the slopes at the two ends. -/
theorem chord_mem {β β' : ℝ → ℝ} {Λa Λb : ℝ} (hβ : ∀ x ∈ Icc Λa Λb, HasDerivAt β (β' x) x)
    (hanti : AntitoneOn β' (Icc Λa Λb)) {Λ Λ₀ : ℝ} (hΛ : Λ ∈ Icc Λa Λb) (hΛ₀ : Λ₀ ∈ Icc Λa Λb)
    (hlt : Λ < Λ₀) :
    β' Λ₀ ≤ (β Λ₀ - β Λ) / (Λ₀ - Λ) ∧ (β Λ₀ - β Λ) / (Λ₀ - Λ) ≤ β' Λ := by
  have hsub : Icc Λ Λ₀ ⊆ Icc Λa Λb := Icc_subset_Icc hΛ.1 hΛ₀.2
  have hcont : ContinuousOn β (Icc Λ Λ₀) := fun x hx => (hβ x (hsub hx)).continuousAt.continuousWithinAt
  have hdiff : ∀ x ∈ Ioo Λ Λ₀, HasDerivAt β (β' x) x := fun x hx => hβ x (hsub (Ioo_subset_Icc_self hx))
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope β β' hlt hcont hdiff
  have hξI : ξ ∈ Icc Λa Λb := hsub (Ioo_subset_Icc_self hξ)
  rw [← hξeq]
  exact ⟨hanti hξI hΛ₀ hξ.2.le, hanti hΛ hξI hξ.1.le⟩

open OAI OAI.SevenEighths

/-- **The ODE-inequality energy region estimate.** Let the curve `β` have antitone slope `β'` on `[Λa, Λb]`,
let its top face be proven, and let one density step be valid from every face of the curve with every slope in
`[β' Λ₀, β' (Λ₀ - h)]` and every length `0 < h ≤ h₀` (`hgood`, the generator lemma read on the curve).
Then every face of the curve is proven. -/
theorem ode_inequality_estimate {β β' : ℝ → ℝ} {Λa Λb h₀ c : ℝ} (hh₀ : 0 < h₀)
    (hβ : ∀ x ∈ Icc Λa Λb, HasDerivAt β (β' x) x) (hanti : AntitoneOn β' (Icc Λa Λb))
    (Good : ℝ → ℝ → ℝ → ℝ → Prop)
    (hgood : ∀ Λ₀ ∈ Icc Λa Λb, ∀ s₀ h : ℝ, β' Λ₀ ≤ s₀ → s₀ ≤ β' (Λ₀ - h) → 0 < h → h ≤ h₀ →
      Λa ≤ Λ₀ - h → Good (β Λ₀) Λ₀ s₀ h)
    (hstep : ∀ B₀ Λ₀ s₀ h : ℝ, Good B₀ Λ₀ s₀ h →
      QRH.Record1252270103Source.GlobalSource B₀ Λ₀ c →
      QRH.Record1252270103Source.GlobalSource (B₀ - s₀ * h) (Λ₀ - h) c)
    (htop : QRH.Record1252270103Source.GlobalSource (β Λb) Λb c) :
    ∀ Λ ∈ Icc Λa Λb, QRH.Record1252270103Source.GlobalSource (β Λ) Λ c := by
  refine curve_induction (fun Λ => QRH.Record1252270103Source.GlobalSource (β Λ) Λ c) hh₀ htop ?_
  intro Λ₀ hΛ₀ Λ hΛ hlt hle hsrc
  have hpos : 0 < Λ₀ - Λ := sub_pos.mpr hlt
  obtain ⟨hlo, hhi⟩ := chord_mem hβ hanti hΛ hΛ₀ hlt
  set s₀ := (β Λ₀ - β Λ) / (Λ₀ - Λ)
  have hchild : β Λ₀ - s₀ * (Λ₀ - Λ) = β Λ := by
    simp only [s₀]; field_simp; ring
  have hΛeq : Λ₀ - (Λ₀ - Λ) = Λ := by ring
  have hg := hgood Λ₀ hΛ₀ s₀ (Λ₀ - Λ) hlo (by rw [hΛeq]; exact hhi) hpos hle (by rw [hΛeq]; exact hΛ.1)
  have := hstep (β Λ₀) Λ₀ s₀ (Λ₀ - Λ) hg hsrc
  rwa [hchild, hΛeq] at this

end
end QRH.ArviOdeShape

#print axioms QRH.ArviOdeShape.ode_inequality_estimate
