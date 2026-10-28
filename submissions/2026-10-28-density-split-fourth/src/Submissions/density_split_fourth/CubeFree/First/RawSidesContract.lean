/- Copyright (c) 2026 Sil. Apache-2.0.
Seam 0: summed first raw side bounds (CF §4).

CF keeps the first artificial-divisor sum inside the Cauchy inequality: the side contract
bounds `∑_u rawEnergy_u` (over squarefree artificial divisors `u`) by a joint budget with
no `1/N(u)` factor, in place of FP's per-divisor `RawSideBounds` (budget `E/N(u)`).

`SummedRawSideBounds` is GENERIC in the per-divisor raw energies, the pair presentation
and the budgets. Its instance on the forked cube-free definitions is the BALANCED contract
`Second.Concrete.BalancedSummedRawSideBounds`; the per-side instance and the bridge from FP's
per-divisor `RawSideBounds` live in `CubeFree/First/RawSides.lean`, typed on the forks.
Modified by Sil (2026-10-26, WP-K2a retarget): the import of the unforked FP
`RepairedFirstRawBlock` (fifth-free columns; 185 FP copies of forked modules) is replaced by
the OAI fixed-pair module; the FP-typed instance part moved to `First/RawSides.lean`. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.First
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily RayFourExpansion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-! ### Generic contract -/

/-- Generic Seam 0. `rawL u τ v K`, `rawR u τ v K` are the raw left/right side energies of
the artificial divisor `u` at character `τ`, height `v` and physical radius `K`;
`left χ ξ`, `right χ ξ` the two characters of the fixed pair at ray characters `χ, ξ`;
`budgetL`, `budgetR` the joint (summed) budgets. -/
def SummedRawSideBounds (Us : Finset Id) (rawL rawR : Id → Character → ℝ → ℝ → ℝ)
    (left right : RayCharacter → RayCharacter → Character)
    (budgetL budgetR : Character → ℝ) (KL KR : ℝ) (J : ℕ) : Prop :=
  ∀ χ ξ : RayCharacter,
    (∀ v : ℝ, ∑ u ∈ Us, rawL u (left χ ξ) v KL ≤ budgetL (left χ ξ)*(1+‖v‖)^(2*J)) ∧
    (∀ v : ℝ, ∑ u ∈ Us, rawR u (right χ ξ) v KR ≤ budgetR (right χ ξ)*(1+‖v‖)^(2*J))

/-- Generic per-divisor contract with divisor weights `wt u` (FP: `1/N(u)`). -/
def PerDivisorRawSideBounds (Us : Finset Id) (rawL rawR : Id → Character → ℝ → ℝ → ℝ)
    (left right : RayCharacter → RayCharacter → Character)
    (budgetL budgetR : Character → ℝ) (wt : Id → ℝ) (KL KR : ℝ) (J : ℕ) : Prop :=
  ∀ u ∈ Us, ∀ χ ξ : RayCharacter,
    (∀ v : ℝ, rawL u (left χ ξ) v KL ≤ budgetL (left χ ξ)*wt u*(1+‖v‖)^(2*J)) ∧
    (∀ v : ℝ, rawR u (right χ ξ) v KR ≤ budgetR (right χ ξ)*wt u*(1+‖v‖)^(2*J))

theorem SummedRawSideBounds.mono_budget {Us : Finset Id} {rawL rawR : Id → Character → ℝ → ℝ → ℝ}
    {left right : RayCharacter → RayCharacter → Character}
    {budgetL budgetR budgetL' budgetR' : Character → ℝ} {KL KR : ℝ} {J : ℕ}
    (hL : ∀ τ, budgetL τ ≤ budgetL' τ) (hR : ∀ τ, budgetR τ ≤ budgetR' τ)
    (h : SummedRawSideBounds Us rawL rawR left right budgetL budgetR KL KR J) :
    SummedRawSideBounds Us rawL rawR left right budgetL' budgetR' KL KR J := by
  intro χ ξ
  obtain ⟨h1, h2⟩ := h χ ξ
  have hp : ∀ v : ℝ, 0 ≤ (1+‖v‖)^(2*J) := fun v => by positivity
  exact ⟨fun v => (h1 v).trans (mul_le_mul_of_nonneg_right (hL _) (hp v)),
    fun v => (h2 v).trans (mul_le_mul_of_nonneg_right (hR _) (hp v))⟩

/-- Per-divisor bounds and a divisor-mass bound give the summed bounds. -/
theorem PerDivisorRawSideBounds.toSummed {Us : Finset Id}
    {rawL rawR : Id → Character → ℝ → ℝ → ℝ}
    {left right : RayCharacter → RayCharacter → Character}
    {budgetL budgetR : Character → ℝ} {wt : Id → ℝ} {Mass KL KR : ℝ} {J : ℕ}
    (hbL : ∀ τ, 0 ≤ budgetL τ) (hbR : ∀ τ, 0 ≤ budgetR τ)
    (hmass : ∑ u ∈ Us, wt u ≤ Mass)
    (h : PerDivisorRawSideBounds Us rawL rawR left right budgetL budgetR wt KL KR J) :
    SummedRawSideBounds Us rawL rawR left right (fun τ => Mass*budgetL τ)
      (fun τ => Mass*budgetR τ) KL KR J := by
  have key : ∀ (raw : Id → ℝ) (b X : ℝ), 0 ≤ b → 0 ≤ X →
      (∀ u ∈ Us, raw u ≤ b*wt u*X) → ∑ u ∈ Us, raw u ≤ Mass*b*X := by
    intro raw b X hb hX hu
    calc ∑ u ∈ Us, raw u ≤ ∑ u ∈ Us, b*X*wt u :=
          Finset.sum_le_sum (fun u hu' => (hu u hu').trans_eq (by ring))
      _ = b*X*∑ u ∈ Us, wt u := by rw [Finset.mul_sum]
      _ ≤ b*X*Mass := mul_le_mul_of_nonneg_left hmass (mul_nonneg hb hX)
      _ = Mass*b*X := by ring
  intro χ ξ
  refine ⟨fun v => key (fun u => rawL u (left χ ξ) v KL) _ _ (hbL _) (by positivity)
      (fun u hu => (h u hu χ ξ).1 v),
    fun v => key (fun u => rawR u (right χ ξ) v KR) _ _ (hbR _) (by positivity)
      (fun u hu => (h u hu χ ξ).2 v)⟩

end
end QRH.DensitySplitThird.CubeFree.First
