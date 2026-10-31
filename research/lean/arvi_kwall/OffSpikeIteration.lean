import Mathlib

/-!
# The off-spike recursion: de Faveri's iteration with the twisted thetas removed

Research file (QRH, K-wall). de Faveri (arXiv 2610.04045, Prop 7.1) proves the optimal n-th order large sieve by
iterating an exponent: one Poisson step plus monotonicity turns `L ≲ A^α + …` into `L ≲ A^{α'} + …` with
`α' = 2 - (n-1)/(nα-1)`, whose attracting fixed point `1 + 1/n` is the theta exponent at the balanced point.

Removing the twisted source thetas with kernel norm `≤ M` changes two things (journal 2026-10-31, "de Faveri's
recursion, run off the spikes"): Poisson keeps only the dual kernels above `M`, and monotonicity conserves `A·M`, so
the theta term is `A·c` with `c = (B²/(AM))^{1/n} = B^γ` fixed along the orbit. One step then reads
`L(A') ≲ A' + A'^{1-α} B^{2α-1} + A'·c`. This file proves the arithmetic of that iteration:

* `c_eq`: with twist range `M = B^{1-nγ}` at `A = B`, `c = B^γ`;
* `balance`, `balance_ge`: at `A' = B^{(2α-1-γ)/α}` both terms equal `B^{step γ α}` with
  `step γ α = 2 + γ - (1+γ)/α`, and `A' ≥ B` exactly when `α ≥ 1 + γ`;
* `step_sub`, `step_sub_le`: `step γ α - (1+γ) = (α - (1+γ))/α`, a contraction by `1/(1+γ)`;
* `tendsto_iter`: from any `α₀ ≥ 1 + γ` the iterates converge to `1 + γ` (for `γ > 0`);
* `defaveri_step_sub`: de Faveri's own map, with fixed point `1 + 1/n`.

The analytic steps (Poisson off the spikes, monotonicity with the twist range, the dual's own thetas) are not
formalized; the obstacles are listed in the journal entry.
-/

namespace QRH.ArviKWall.OffSpike

open Filter Topology

/-- One step of the off-spike iteration. -/
noncomputable def step (γ α : ℝ) : ℝ := 2 + γ - (1 + γ) / α

/-- With twist range `M = B^{1 - nγ}` at `A = B`, the multiplicity bound `(B²/(A M))^{1/n}` is `B^γ`. -/
theorem c_eq {B : ℝ} (hB : 0 < B) {n : ℝ} (hn : n ≠ 0) (γ : ℝ) :
    (B ^ (2 : ℝ) / (B * B ^ (1 - n * γ))) ^ (1 / n) = B ^ γ := by
  have h1 : B * B ^ (1 - n * γ) = B ^ (2 - n * γ) := by
    rw [show (2 : ℝ) - n * γ = 1 + (1 - n * γ) by ring, Real.rpow_add hB, Real.rpow_one]
  rw [h1, ← Real.rpow_sub hB, ← Real.rpow_mul hB.le]
  congr 1
  field_simp
  ring

theorem step_sub {γ α : ℝ} (hα : α ≠ 0) : step γ α - (1 + γ) = (α - (1 + γ)) / α := by
  unfold step
  field_simp
  ring

/-- The balancing point of one step: both the theta term `A'·B^γ` and the hypothesis term `A'^{1-α} B^{2α-1}`
equal `B^{step γ α}` at `A' = B^{(2α-1-γ)/α}`. -/
theorem balance {B : ℝ} (hB : 0 < B) (γ : ℝ) {α : ℝ} (hα : α ≠ 0) :
    B ^ ((2 * α - 1 - γ) / α) * B ^ γ = B ^ step γ α ∧
      (B ^ ((2 * α - 1 - γ) / α)) ^ (1 - α) * B ^ (2 * α - 1) = B ^ step γ α := by
  constructor
  · rw [← Real.rpow_add hB]
    congr 1
    unfold step
    field_simp
    ring
  · rw [← Real.rpow_mul hB.le, ← Real.rpow_add hB]
    congr 1
    unfold step
    field_simp
    ring

/-- The balancing point lies above the starting point `A = B` once `α ≥ 1 + γ`, so monotonicity applies. -/
theorem balance_ge {B : ℝ} (hB : 1 ≤ B) {γ α : ℝ} (hγ : 0 ≤ γ) (hα : 1 + γ ≤ α) :
    B ≤ B ^ ((2 * α - 1 - γ) / α) := by
  have hα0 : 0 < α := by linarith
  conv_lhs => rw [← Real.rpow_one B]
  apply Real.rpow_le_rpow_of_exponent_le hB
  rw [le_div_iff₀ hα0]
  linarith

theorem fixed_le_step {γ α : ℝ} (hγ : 0 ≤ γ) (h : 1 + γ ≤ α) : 1 + γ ≤ step γ α := by
  have hα : 0 < α := by linarith
  have h1 := step_sub (γ := γ) hα.ne'
  have h2 : 0 ≤ (α - (1 + γ)) / α := div_nonneg (by linarith) hα.le
  linarith

theorem step_lt {γ α : ℝ} (hγ : 0 ≤ γ) (h : 1 + γ < α) : step γ α < α := by
  have hα : 0 < α := by linarith
  have h1 := step_sub (γ := γ) hα.ne'
  have h2 : (α - (1 + γ)) / α < α - (1 + γ) := by
    rw [div_lt_iff₀ hα]
    nlinarith
  linarith

/-- Contraction: the distance to `1 + γ` shrinks at least by the factor `1/(1+γ)`. -/
theorem step_sub_le {γ α : ℝ} (hγ : 0 ≤ γ) (h : 1 + γ ≤ α) :
    step γ α - (1 + γ) ≤ (α - (1 + γ)) / (1 + γ) := by
  have hα : 0 < α := by linarith
  rw [step_sub hα.ne']
  exact div_le_div_of_nonneg_left (by linarith) (by linarith) h

/-- The iterates of the off-spike step from `α₀`. -/
noncomputable def iter (γ α₀ : ℝ) : ℕ → ℝ
  | 0 => α₀
  | k + 1 => step γ (iter γ α₀ k)

theorem iter_bounds {γ α₀ : ℝ} (hγ : 0 ≤ γ) (h : 1 + γ ≤ α₀) (k : ℕ) :
    1 + γ ≤ iter γ α₀ k ∧ iter γ α₀ k - (1 + γ) ≤ (α₀ - (1 + γ)) / (1 + γ) ^ k := by
  induction k with
  | zero => exact ⟨h, by simp [iter]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fixed_le_step hγ h1, ?_⟩
    show step γ (iter γ α₀ k) - (1 + γ) ≤ (α₀ - (1 + γ)) / (1 + γ) ^ (k + 1)
    calc step γ (iter γ α₀ k) - (1 + γ) ≤ (iter γ α₀ k - (1 + γ)) / (1 + γ) := step_sub_le hγ h1
      _ ≤ ((α₀ - (1 + γ)) / (1 + γ) ^ k) / (1 + γ) :=
          div_le_div_of_nonneg_right h2 (by linarith)
      _ = (α₀ - (1 + γ)) / (1 + γ) ^ (k + 1) := by rw [pow_succ, div_div]

/-- **The off-spike iteration converges to `1 + γ`**, the exponent of `(LS off V)` with twist range
`B^{1 - nγ}`. -/
theorem tendsto_iter {γ α₀ : ℝ} (hγ : 0 < γ) (h : 1 + γ ≤ α₀) :
    Tendsto (iter γ α₀) atTop (𝓝 (1 + γ)) := by
  have hq : Tendsto (fun k : ℕ => ((1 + γ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
  have hlim : Tendsto (fun k : ℕ => (1 + γ) + (α₀ - (1 + γ)) * ((1 + γ)⁻¹) ^ k) atTop
      (𝓝 (1 + γ)) := by
    simpa using (hq.const_mul (α₀ - (1 + γ))).const_add (1 + γ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim ?_ ?_
  · intro k
    exact (iter_bounds hγ.le h k).1
  · intro k
    have h2 := (iter_bounds hγ.le h k).2
    rw [div_eq_mul_inv, ← inv_pow] at h2
    show iter γ α₀ k ≤ (1 + γ) + (α₀ - (1 + γ)) * ((1 + γ)⁻¹) ^ k
    linarith

/-- de Faveri's map (Prop 7.1), for comparison. -/
noncomputable def defaveriStep (n α : ℝ) : ℝ := 2 - (n - 1) / (n * α - 1)

/-- de Faveri's map contracts toward `1 + 1/n`, the theta exponent at the balanced point. -/
theorem defaveri_step_sub {n α : ℝ} (hn : n ≠ 0) (h : n * α - 1 ≠ 0) :
    defaveriStep n α - (1 + 1 / n) = (n - 1) * (α - (1 + 1 / n)) / (n * α - 1) := by
  unfold defaveriStep
  field_simp
  ring

end QRH.ArviKWall.OffSpike

#print axioms QRH.ArviKWall.OffSpike.tendsto_iter
#print axioms QRH.ArviKWall.OffSpike.balance
#print axioms QRH.ArviKWall.OffSpike.balance_ge
#print axioms QRH.ArviKWall.OffSpike.c_eq
#print axioms QRH.ArviKWall.OffSpike.step_lt
#print axioms QRH.ArviKWall.OffSpike.defaveri_step_sub
