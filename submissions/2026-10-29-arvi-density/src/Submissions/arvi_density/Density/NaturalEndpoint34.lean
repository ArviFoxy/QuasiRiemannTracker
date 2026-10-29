/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Lemma 2.1 (natural-dictionary zero density) on the range `3/4 ≤ a`, i.e. density floor `q ≥ 1/2`.
Fork of Collet's `Cycle61/Density/ActualZeros.lean` (`fixed_dictionary_actual_raw_zero_density`) and
`Cycle61/Density/NaturalEndpoint.lean` (`natural_zero_to_literal_dictionary`,
`fixed_natural_dictionary_raw_density`), stated at `33/40 ≤ a` there; changed: the lower end is `3/4`,
and the two range-dependent inputs are Collet's own `3/4` restatements in
`Record1252270103Source/High/OrdinaryRangeDensity.lean`. The proof bodies are otherwise Collet's. -/
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.OrdinaryRangeDensity

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI
noncomputable section
open scoped Classical ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
namespace Range34
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open CenteredMomentNaturalRowSource HeckeFiniteDeletion
local notation "O" => HeckeFamily.O

abbrev DensityParameter34 := {p : ℝ × ℝ | 3/4 ≤ p.1 ∧ p.1 ≤ 7/8 ∧ 0 ≤ p.2}

theorem fixed_dictionary_actual_raw_zero_density {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 3/4 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ orientedActualZeroRow D.data reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hf⟩ :=
    Record1252270103HighOrdinaryRange.fixed_dictionary_eventual_with_exceptions D loss hloss
  let P : DensityParameter34 → FreeRow → Prop := fun p u =>
    rawZeroBin D.data p.val.1 (7/8) p.val.2 ⟨u.val, u.property.1⟩ ∨ D.exceptionalCore u
  let exponent : DensityParameter34 → ℝ := fun p => unmarkedDensity (2*p.val.1-1)+loss
  let weight : DensityParameter34 → ℝ := fun p => (1+p.val.2)^J
  have hρ (p : DensityParameter34) : 2/7 ≤ exponent p := by
    dsimp [exponent]
    linarith [unmarkedDensity_ge_two_sevenths (show 2*p.val.1-1 ≤ 3/4 by linarith [p.property.2.1])]
  have hw (p : DensityParameter34) : 1 ≤ weight p := one_le_pow₀ (by linarith [p.property.2.2])
  have hevent : ∀ᶠ Y : ℝ in atTop, ∀ p : DensityParameter34, ∀ F : Finset FreeRow,
      (∀ u ∈ F, rowNorm u ≤ Y ∧ P p u) → (F.card : ℝ) ≤ C*weight p*Y^exponent p := by
    filter_upwards [hf] with Y hf
    intro p
    exact hf p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2
  obtain ⟨C', hC', _, hfree⟩ := uniform_free_density_weighted_of_eventually P C exponent weight
    (fun p => by linarith [hρ p]) hw hevent
  obtain ⟨D₀, hD₀, hraw⟩ := raw_core_density_uniform
  refine ⟨J, C'*D₀, mul_pos hC' hD₀, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  let p : DensityParameter34 := ⟨(a,T), ha, ha', hT⟩
  have hb := hraw (P p) (C'*weight p) (exponent p) (by have := hw p; positivity) (hρ p)
    (fun Y hY F hF => hfree Y hY p F hF) H hH rows
    (fun u hu => ⟨(hrows u hu).1,
      Record1252270103HighOrdinaryRange.oriented_zero_core_predicate D reverse a T ha u
        (hrows u hu).2⟩)
  convert hb using 1
  dsimp [p, weight, exponent]
  ring

theorem natural_zero_to_literal_dictionary {Label : Type*}
    (base : Label → Character) (reverse : Label → Bool) (a T : ℝ)
    (ha : 3/4 ≤ a) (u : NonzeroElement)
    (hz : naturalActualZeroRow base reverse a T u) :
    orientedActualZeroRow (FixedUnmarkedDictionary.ofBases base).data reverse a T u := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  let χ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
  let ψ := if reverse j then ((momentData (base j)).character u).inverse
    else (momentData (base j)).character u
  have hc : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I := by
    intro I
    cases hr : reverse j
    · simpa only [χ, ψ, hr, Bool.false_eq_true, ite_false, naturalRawFamily] using
        natural_raw_coefficients (base j) u I
    · dsimp [χ, ψ]
      simp only [hr, ite_true]
      rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj]
      dsimp only [naturalRawFamily]
      rw [natural_raw_coefficients]
  have hh := positive_zeros_eq_of_coefficients χ ψ hc (show 0 < s.re by linarith) hpole
  exact ⟨j, s, hh.1.mp hz, hh.2, hs, ht⟩

/-- **Lemma 2.1 at `3/4 ≤ a`** (density floor `q ≥ 1/2`), in the exact shape of Collet's
`fixed_natural_dictionary_raw_density`: dictionary first, then the degree `J`. -/
theorem fixed_natural_dictionary_raw_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 3/4 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ naturalActualZeroRow base reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_dictionary_actual_raw_zero_density
    (FixedUnmarkedDictionary.ofBases base) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  exact hb reverse a T ha ha' hT H hH rows (fun u hu =>
    ⟨(hrows u hu).1, natural_zero_to_literal_dictionary base reverse a T ha u (hrows u hu).2⟩)

end Range34
end SevenEighths.LocalMoment
end
end OAI

#print axioms OAI.SevenEighths.LocalMoment.Range34.fixed_natural_dictionary_raw_density
