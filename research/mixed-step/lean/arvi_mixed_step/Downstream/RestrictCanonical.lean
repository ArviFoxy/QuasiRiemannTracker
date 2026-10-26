/- Mixed source step, N3 (pieces): new in this submission; uses Collet's definitions
(`initialInput`, `Initial`, `Canonical`) and the transfer's `Input.restrict` by import.

The residual of Collet's initial input is again an initial input, of the restricted slot data
(`L45_DESIGN.md` §3, N1: "`initialInput` is per-slot, so rfl"). The forked spines take a canonical
record `Canonical … F.s` for the second-layer parent `F.s = s.restrict J` (HANDOFF.md, F4 tops):

* `initialInput_restrict`: `(initialInput … θ w v t …).restrict J = initialInput … (θ∘val) (w∘val)
  (v∘val) t …` (`rfl`);
* `Initial.restrict`, `Initial.input_restrict` (`rfl`);
* `canonicalRestrict`: a canonical record of `s` gives one of `s.restrict J`.

No `open scoped Classical` here: the slot type `{i // i ∉ J}` keeps the `Fintype` instance built
from the `DecidableEq α` binder, as in `Input.restrict`. -/
import Submissions.arvi_mixed_step.Residual.Restrict
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularLowPointData
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularHighPointSomeData

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.MixedStep.Downstream
noncomputable section
open OAI OAI.SevenEighths
open scoped ContDiff
open CenteredMomentCommonRadialData QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
open QRH.Record1252270103Source.Admission.SelectedRegularHighPoint
local notation "O" => HeckeFamily.O

section Restrict
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance restrictCanonicalFinite : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
  (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Set.Icc (1:ℝ) 2)
  (Z : ℝ) (hZ : 0 < Z) (η η₀ : HeckeFamily.Character) (R₀ : Ideal O)

/-- **The residual of an initial input is an initial input.** -/
theorem initialInput_restrict (θ : α → RayQuotient.Characters rayM H) (w v : α → ℝ) (t : ℝ)
    {a b : ℝ} (p : CenteredMomentFiniteProfileExceptional.Profiles a b) (ha : 0 < a)
    (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hprod : Y₁ * Y₂ = X₁ * X₂) (J : Finset α) :
    (initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t p ha X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂
        hprod).restrict J =
      initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ (fun i => θ i.val) (fun i => w i.val)
        (fun i => v i.val) t p ha X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod := rfl

end Restrict

namespace Initial'
variable {α : Type} [Fintype α] [DecidableEq α] {rayM : Ideal O} [NeZero rayM]
  {H : Subgroup (O ⧸ rayM)ˣ} {Z : ℝ}

/-- The initial data restricted off a block `J`. -/
def restrict (i : Initial (α := α) rayM H Z) (J : Finset α) : Initial (α := {i // i ∉ J}) rayM H Z :=
  ⟨fun j => i.θ j.val, fun j => i.w j.val, fun j => i.freq j.val, i.t₀, i.p, i.X₁, i.X₂, i.Y₁, i.Y₂,
    i.hX₁, i.hX₂, i.hY₁, i.hY₂, i.same⟩

theorem input_restrict (i : Initial (α := α) rayM H Z) (J : Finset α)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hsW : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hZ : 1 < Z) (η η₀ : HeckeFamily.Character)
    (R₀ : Ideal O) :
    (i.input hH W hW hsW hZ η η₀ R₀).restrict J = (restrict i J).input hH W hW hsW hZ η η₀ R₀ :=
  rfl

end Initial'

section Canonical
variable {α : Type} [Fintype α] [DecidableEq α] {M : Ideal O} [NeZero M]
  {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {hW : ContDiff ℝ ∞ W} {hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2}
  {ηanchor η₀ : HeckeFamily.Character} {R₀ : Ideal O} {Z : ℝ} {hZ : 1 < Z} {s : Input α}

/-- **A canonical record of `s` gives one of `s.restrict J`** (widths `w ∘ val`). -/
def canonicalRestrict (c : Canonical M H hH W hW hWs ηanchor η₀ R₀ Z hZ s) (J : Finset α) :
    Canonical M H hH W hW hWs ηanchor η₀ R₀ Z hZ (s.restrict J) where
  w := fun i => c.w i.val
  v := fun i => c.v i.val
  ray := fun i => c.ray i.val
  origin := c.origin
  p := c.p
  X₁ := c.X₁
  X₂ := c.X₂
  Y₁ := c.Y₁
  Y₂ := c.Y₂
  X₁_pos := c.X₁_pos
  X₂_pos := c.X₂_pos
  Y₁_pos := c.Y₁_pos
  Y₂_pos := c.Y₂_pos
  product := c.product
  input := (congrArg (fun x : Input α => x.restrict J) c.input).trans rfl

theorem canonicalRestrict_w (c : Canonical M H hH W hW hWs ηanchor η₀ R₀ Z hZ s) (J : Finset α)
    (i : {i // i ∉ J}) : (canonicalRestrict c J).w i = c.w i.val := rfl

end Canonical

end
end QRH.MixedStep.Downstream

#print axioms QRH.MixedStep.Downstream.initialInput_restrict
#print axioms QRH.MixedStep.Downstream.Initial'.input_restrict
#print axioms QRH.MixedStep.Downstream.canonicalRestrict
