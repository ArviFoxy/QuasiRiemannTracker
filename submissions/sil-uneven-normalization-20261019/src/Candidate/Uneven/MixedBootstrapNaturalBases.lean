/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Cycle63.Marked.WholeNaturalBatch

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.MixedBootstrapNaturalBases
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckeFiniteDeletion LocalMoment Cycle63Moment Cycle63MarkedPlain
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Each whole-family base is represented by a fixed natural row over its
own relative-slot anchor, followed by one fixed conductor deletion. -/
def base (ηcoarse η₀ : Character) (u₀ : O) (hu₀ : u₀≠0) (R₀ : Ideal O)
    (j : WholeSourceIndex M H) : Character :=
  excluded (naturalRow (wholeSourceBase M H hH η₀ ηcoarse j) u₀ hu₀).character
    (R₀*wholeAnchorMask M H hH η₀)

theorem base_coefficients (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀)
    (hu₀ : u₀≠0) (R₀ : Ideal O) (hR₀ : R₀≠0)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (cleanWholeBase M H hH (excluded F₀.character R₀) η₀ j) I =
      idealCoeff (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) I := by
  let R := R₀*wholeAnchorMask M H hH η₀
  have hR : R≠0 := mul_ne_zero hR₀ (wholeAnchorMask_ne_zero M H hH η₀)
  let χ := excluded (excluded F₀.character R₀) (wholeAnchorMask M H hH η₀)
  have hc (J : Ideal O) : idealCoeff χ J=idealCoeff (excluded F₀.character R) J := by
    dsimp only [χ,R]
    rw [excluded_ideal _ _ (wholeAnchorMask_ne_zero M H hH η₀),
      excluded_ideal _ _ hR₀,excluded_ideal _ _ hR,IsCoprime.mul_right_iff]
    split_ifs <;> simp_all
  let G := fun k : WholeSourceIndex M H=>naturalRow (wholeSourceBase M H hH η₀ ηcoarse k) u₀ hu₀
  have hh := whole_source_family_mask M H hH η₀ ηcoarse χ u₀ hu₀ F₀ R hR hc G j I
  change idealCoeff (wholeSourceFamily M H hH η₀ χ j) I =
    idealCoeff (excluded (G j).character R) I at hh
  convert hh using 1 <;> cases j <;> rfl

theorem natural_coefficients (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀)
    (hu₀ : u₀≠0) (R₀ : Ideal O) (hR₀ : R₀≠0)
    (j : WholeSourceIndex M H) (u : O) (hu : u≠0) (I : Ideal O) :
    idealCoeff (naturalRow (cleanWholeBase M H hH (excluded F₀.character R₀) η₀ j) u hu).character I =
      idealCoeff (naturalRow (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u hu).character I := by
  rw [(naturalRow _ u hu).ideal,(naturalRow _ u hu).ideal,
    base_coefficients M H hH ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ j I]

/-- The new natural presentation preserves every positive nonpole zero.
No extra analytic hypothesis is introduced by changing the fixed bases. -/
theorem whole_family_zero (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀)
    (hu₀ : u₀≠0) (R₀ : Ideal O) (hR₀ : R₀≠0)
    (j : WholeSourceIndex M H) (u : O) (hu : u≠0) {s : ℂ} (hs : 0<s.re)
    (hpole : s≠1 ∨
      (naturalRow (wholeSourceBase M H hH η₀ (excluded F₀.character R₀) j) u hu).character.residue≠1)
    (hz : LFunction (naturalRow (wholeSourceBase M H hH η₀ (excluded F₀.character R₀) j) u hu).character s=0) :
    LFunction (naturalRow (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u hu).character s=0 ∧
      (s≠1 ∨ (naturalRow (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u hu).character.residue≠1) := by
  have hc := whole_family_clean_zero M H hH (excluded F₀.character R₀) η₀ u hu j hs hpole hz
  have he := positive_zeros_eq_of_coefficients _ _
    (fun I=>natural_coefficients M H hH ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ j u hu I) hs hc.2
  exact ⟨he.1.mp hc.1,he.2⟩

end
end OAI.SevenEighths.MixedBootstrapNaturalBases
#print axioms OAI.SevenEighths.MixedBootstrapNaturalBases.base_coefficients
#print axioms OAI.SevenEighths.MixedBootstrapNaturalBases.whole_family_zero
