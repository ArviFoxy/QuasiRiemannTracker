/-
Principal (perfect sixth power) rows are removed by `initialKeep`.

For the trivial Hecke character `triv` (modulus `(1)`), every row `z = w^6` (w ≠ 0) is a `FixedInducingRow`
for every `Q` and every `m ≠ 0` divisible by `λ` and `2`; in particular `initialKeep triv Q (w^6)` fails for
`m = fixedBadMask * idealGenerator 1`.  Proof: the row character is the principal character modulo `m w`, which is
induced by the trivial primitive character (modulus `(1)`, vacuously primitive, `Q ≤ (1)`).
Only imports the project; no `sorry`; axioms: propext, Classical.choice, Quot.sound.

Check:  cd <qrh root> && lake env lean PrincipalRowRemoved.lean
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState

open OAI OAI.SevenEighths
open scoped Classical

namespace PrincipalRowProbe

local notation "O" => HeckeFamily.O

instance subsingleton_top : Subsingleton (O ⧸ (⊤ : Ideal O)) :=
  Ideal.Quotient.subsingleton_iff.mpr rfl

/-- the trivial Hecke character (modulus `(1)`) -/
noncomputable def triv : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue ⊤ top_ne_bot 1
    (fun _ => MulChar.one_apply (isUnit_of_subsingleton _))

theorem triv_modulus : triv.modulus = ⊤ := rfl

instance subsingleton_triv : Subsingleton (O ⧸ triv.modulus) := subsingleton_top

theorem elementCoeff_triv (n : O) : HeckeFamily.elementCoeff triv n = 1 := by
  unfold HeckeFamily.elementCoeff
  exact MulChar.one_apply (isUnit_of_subsingleton _)

theorem idealCoeff_triv_span {n : O} (hn : n ≠ 0) :
    HeckeFamily.idealCoeff triv (Ideal.span {n}) = 1 := by
  rw [HeckeFamily.idealCoeff_span triv hn, elementCoeff_triv]

/-- Every perfect-sixth-power row of the trivial character is a `FixedInducingRow`. -/
theorem sixth_power_row_fixedInducing (Q : Ideal O) (m w : O) (hm : m ≠ 0) (hw : w ≠ 0)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2 : O) ∣ m) :
    CenteredExceptionalProfile.FixedInducingRow triv Q m 1 (w ^ 6) := by
  obtain ⟨χ, hχ⟩ := HeckeRowClosure.exists_row_character triv m 1 (1 * w ^ 6) hm one_ne_zero
    (by simpa using pow_ne_zero 6 hw) hmLam hm2
  refine ⟨χ, triv, ?_, ?_, le_top, hχ⟩
  · intro I hI
    exact absurd (Subsingleton.elim _ _) hI
  · intro I
    have key := HeckeRowClosure.idealCoeff_eq_row triv χ m 1 (1 * w ^ 6) hχ I
    have e6 : m ^ 6 * (1 : O) ^ 4 * (1 * w ^ 6) = (m * w) ^ 6 := by ring
    rw [e6] at key
    by_cases hI : I = 0
    · subst hI
      change HeckeFamily.idealCoeff χ 0 =
        if IsCoprime (0 : Ideal O) χ.modulus then HeckeFamily.idealCoeff triv 0 else 0
      rw [HeckeFamily.idealCoeff_zero, HeckeFamily.idealCoeff_zero]
      split_ifs <;> rfl
    obtain ⟨n, rfl⟩ : ∃ n, I = Ideal.span {n} :=
      ⟨ConcretePrimeRowBridge.idealGenerator I, (ConcretePrimeRowBridge.span_idealGenerator I).symm⟩
    have hn : n ≠ 0 := by
      intro h
      apply hI
      simp [h]
    by_cases hc : IsCoprime (Ideal.span {n}) χ.modulus
    · simp only [hc, ite_true, idealCoeff_triv_span hn]
      have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) :=
        (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hc
      have hne : HeckeFamily.idealCoeff χ (Ideal.span {n}) ≠ 0 := by
        rw [HeckeFamily.idealCoeff_span χ hn]
        unfold HeckeFamily.elementCoeff
        obtain ⟨u, hu'⟩ := hu
        rw [← hu', ← MulChar.coe_toUnitHom]
        exact Units.ne_zero _
      have hsupp : CanonicalQuadraticSieve.Supported (Ideal.span {n}) := by
        by_contra hns
        have h0 := CanonicalRowCompletion.rowTwist_zero_of_not_supported
          (HeckeRowClosure.elementHom triv) m 1 (1 * w ^ 6) n hmLam hm2 hns
        apply hne
        rw [HeckeFamily.idealCoeff_span χ hn, hχ n, h0]
      have hmask := CanonicalRowCompletion.idealRowHom_sixth_mask (m * w) (Ideal.span {n}) hsupp
      rw [key, idealCoeff_triv_span hn, one_mul, hmask]
      rw [key, idealCoeff_triv_span hn, one_mul, hmask] at hne
      by_cases hcm : IsCoprime (Ideal.span {n}) (Ideal.span {m * w})
      · simp only [hcm, ite_true]
      · simp only [hcm, ite_false] at hne
        exact absurd rfl hne
    · simp only [hc, ite_false]
      have hnu : ¬ IsUnit (Ideal.Quotient.mk χ.modulus n) := fun h =>
        hc ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp h)
      rw [HeckeFamily.idealCoeff_span χ hn]
      unfold HeckeFamily.elementCoeff
      exact χ.residue.map_nonunit hnu

/-- `initialKeep` (with the actual mask `fixedBadMask * idealGenerator 1`) removes every perfect sixth power row. -/
theorem sixth_power_row_removed (Q : Ideal O) (w : O) (hw : w ≠ 0) :
    ¬ CenteredMomentDetectorEnergyInitialState.initialKeep triv Q (w ^ 6) := by
  intro h
  refine h.2 (sixth_power_row_fixedInducing Q _ w ?_ hw ?_ ?_)
  · exact mul_ne_zero CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero 1 one_ne_zero)
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)

end PrincipalRowProbe

#print axioms PrincipalRowProbe.sixth_power_row_fixedInducing
#print axioms PrincipalRowProbe.sixth_power_row_removed
