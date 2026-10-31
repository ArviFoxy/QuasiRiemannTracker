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
* `defaveri_step_sub`: de Faveri's own map, with fixed point `1 + 1/n`;
* Sil's form (monotonicity by inclusion, as in his formal `FourthPower/SieveImprovement.lean`): `silStep`, with
  `silStep_sil` (at `γ = 1/n`, `n = 6` it is Sil's `step α = (12α-7)/(6α-1)`), `silEnlargement_sil`,
  `sil_theta_eq`, `silBalance`, `one_le_silEnlargement` and `tendsto_silIter` (fixed point `1 + γ` again, now with
  the twist range fixed along the orbit).

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

/-! ## Sil's form: monotonicity by inclusion

Sil's formal optimal sieve (`FourthPower/SieveImprovement.lean`, `improve`) does not twist the vector in the
monotonicity step. Its rows are all moduli of norm `≤ T`, so `θ(M, N) ≤ θ(T, N)` for `T ≥ M` by inclusion, and one
step bounds `θ(T, N)` by `T + T^{1-α} N^{2α-1} + T^{5/6} N^{1/3}` at `T = max(M, N^{enlargement α})`. Off the
twisted source thetas of kernel `≤ μ` the theta term is `T (N²/(T μ))^{1/n}`, and the twist range `μ` stays fixed
along the orbit (the source vector is not twisted, so no local spikes appear). With `μ = N^{1-nγ}` the theta term is
`T^{1-1/n} N^{1/n+γ}`, and balancing gives the map `silStep`. At `γ = 1/n` (nothing removed) and `n = 6` it is
Sil's `step α = (12α-7)/(6α-1)` (`silStep_sil`), with `enlargement α = (12α-8)/(6α-1)` (`silEnlargement_sil`). Its
attracting fixed point is again `1 + γ`.
-/

/-- One step of the off-spike iteration in Sil's form (monotonicity by inclusion). -/
noncomputable def silStep (n γ α : ℝ) : ℝ :=
  (1 - 1 / n) * (2 * α - 1 - 1 / n - γ) / (α - 1 / n) + 1 / n + γ

/-- The enlarged row range `T = N^{silEnlargement n γ α}` of one step. -/
noncomputable def silEnlargement (n γ α : ℝ) : ℝ := (2 * α - 1 - 1 / n - γ) / (α - 1 / n)

/-- Nothing removed (`γ = 1/n`), `n = 6`: Sil's formal step map. -/
theorem silStep_sil {α : ℝ} (hα : 6 * α - 1 ≠ 0) :
    silStep 6 (1 / 6) α = (12 * α - 7) / (6 * α - 1) := by
  have hα' : α - 1 / 6 ≠ 0 := by
    intro h
    apply hα
    linarith
  unfold silStep
  field_simp
  ring

/-- Nothing removed, `n = 6`: Sil's formal enlargement exponent. -/
theorem silEnlargement_sil {α : ℝ} (hα : 6 * α - 1 ≠ 0) :
    silEnlargement 6 (1 / 6) α = (12 * α - 8) / (6 * α - 1) := by
  have hα' : α - 1 / 6 ≠ 0 := by
    intro h
    apply hα
    linarith
  unfold silEnlargement
  field_simp
  ring

/-- With twist range `μ = N^{1-nγ}`, the theta term `T (N²/(T μ))^{1/n}` is `T^{1-1/n} N^{1/n+γ}`. -/
theorem sil_theta_eq {N T : ℝ} (hN : 0 < N) (hT : 0 < T) {n : ℝ} (hn : n ≠ 0) (γ : ℝ) :
    T * (N ^ (2 : ℝ) / (T * N ^ (1 - n * γ))) ^ (1 / n) =
      T ^ (1 - 1 / n) * N ^ (1 / n + γ) := by
  have hNp : 0 < N ^ (1 - n * γ) := Real.rpow_pos_of_pos hN _
  have h1 : N ^ (2 : ℝ) / (T * N ^ (1 - n * γ)) = N ^ (1 + n * γ) * T⁻¹ := by
    have e : N ^ (1 + n * γ) = N ^ (2 : ℝ) / N ^ (1 - n * γ) := by
      rw [← Real.rpow_sub hN]
      congr 1
      ring
    rw [e, mul_comm T, ← div_div, div_eq_mul_inv _ T]
  rw [h1, Real.mul_rpow (Real.rpow_nonneg hN.le _) (inv_nonneg.mpr hT.le), ← Real.rpow_mul hN.le,
    Real.inv_rpow hT.le, ← Real.rpow_neg hT.le]
  have h2 : (1 + n * γ) * (1 / n) = 1 / n + γ := by
    field_simp
  rw [h2]
  calc T * (N ^ (1 / n + γ) * T ^ (-(1 / n))) = (T ^ (1 : ℝ) * T ^ (-(1 / n))) * N ^ (1 / n + γ) := by
        rw [Real.rpow_one]
        ring
    _ = T ^ (1 - 1 / n) * N ^ (1 / n + γ) := by
        rw [← Real.rpow_add hT]
        ring_nf

/-- The balancing point of one step in Sil's form: at `T = N^{silEnlargement}` the hypothesis term
`T^{1-α} N^{2α-1}` and the theta term `T^{1-1/n} N^{1/n+γ}` both equal `N^{silStep}`. -/
theorem silBalance {N : ℝ} (hN : 0 < N) (n γ : ℝ) {α : ℝ} (hα : α - 1 / n ≠ 0) :
    (N ^ silEnlargement n γ α) ^ (1 - α) * N ^ (2 * α - 1) = N ^ silStep n γ α ∧
      (N ^ silEnlargement n γ α) ^ (1 - 1 / n) * N ^ (1 / n + γ) = N ^ silStep n γ α := by
  constructor
  · rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    unfold silEnlargement silStep
    field_simp
    ring
  · rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    unfold silEnlargement silStep
    ring

theorem silStep_sub {n γ α : ℝ} (hα : α - 1 / n ≠ 0) :
    silStep n γ α - (1 + γ) = (1 - 1 / n) * (α - (1 + γ)) / (α - 1 / n) := by
  unfold silStep
  field_simp
  ring

/-- The enlarged range lies above the balanced point `T ≥ N` exactly when `α ≥ 1 + γ`. -/
theorem one_le_silEnlargement {n γ α : ℝ} (hn : 1 < n) (hγ : 0 ≤ γ) (h : 1 + γ ≤ α) :
    1 ≤ silEnlargement n γ α := by
  have hn' : 1 / n < 1 := by
    rw [div_lt_one (by linarith)]
    exact hn
  have hpos : 0 < α - 1 / n := by linarith
  unfold silEnlargement
  rw [le_div_iff₀ hpos]
  linarith

theorem fixed_le_silStep {n γ α : ℝ} (hn : 1 < n) (hγ : 0 ≤ γ) (h : 1 + γ ≤ α) :
    1 + γ ≤ silStep n γ α := by
  have hn' : 1 / n < 1 := by
    rw [div_lt_one (by linarith)]
    exact hn
  have hpos : 0 < α - 1 / n := by linarith
  have h1 := silStep_sub (n := n) (γ := γ) hpos.ne'
  have h2 : 0 ≤ (1 - 1 / n) * (α - (1 + γ)) / (α - 1 / n) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hpos.le
  linarith

/-- Contraction toward `1 + γ` by the factor `(1 - 1/n)/(1 - 1/n + γ)`. -/
theorem silStep_sub_le {n γ α : ℝ} (hn : 1 < n) (hγ : 0 ≤ γ) (h : 1 + γ ≤ α) :
    silStep n γ α - (1 + γ) ≤ (1 - 1 / n) / (1 - 1 / n + γ) * (α - (1 + γ)) := by
  have hn' : 1 / n < 1 := by
    rw [div_lt_one (by linarith)]
    exact hn
  have hpos : 0 < α - 1 / n := by linarith
  have hq : 0 < 1 - 1 / n + γ := by linarith
  rw [silStep_sub hpos.ne', div_mul_eq_mul_div]
  rw [show (1 - 1 / n) * (α - (1 + γ)) = (1 - 1 / n) * (α - (1 + γ)) from rfl]
  apply div_le_div_of_nonneg_left (mul_nonneg (by linarith) (by linarith)) hq
  linarith

/-- The iterates of Sil's-form step from `α₀`. -/
noncomputable def silIter (n γ α₀ : ℝ) : ℕ → ℝ
  | 0 => α₀
  | k + 1 => silStep n γ (silIter n γ α₀ k)

theorem silIter_bounds {n γ α₀ : ℝ} (hn : 1 < n) (hγ : 0 ≤ γ) (h : 1 + γ ≤ α₀) (k : ℕ) :
    1 + γ ≤ silIter n γ α₀ k ∧
      silIter n γ α₀ k - (1 + γ) ≤ ((1 - 1 / n) / (1 - 1 / n + γ)) ^ k * (α₀ - (1 + γ)) := by
  have hn' : 1 / n < 1 := by
    rw [div_lt_one (by linarith)]
    exact hn
  have hq0 : 0 ≤ (1 - 1 / n) / (1 - 1 / n + γ) := div_nonneg (by linarith) (by linarith)
  induction k with
  | zero => exact ⟨h, by simp [silIter]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fixed_le_silStep hn hγ h1, ?_⟩
    show silStep n γ (silIter n γ α₀ k) - (1 + γ) ≤
      ((1 - 1 / n) / (1 - 1 / n + γ)) ^ (k + 1) * (α₀ - (1 + γ))
    calc silStep n γ (silIter n γ α₀ k) - (1 + γ)
        ≤ (1 - 1 / n) / (1 - 1 / n + γ) * (silIter n γ α₀ k - (1 + γ)) := silStep_sub_le hn hγ h1
      _ ≤ (1 - 1 / n) / (1 - 1 / n + γ) * (((1 - 1 / n) / (1 - 1 / n + γ)) ^ k * (α₀ - (1 + γ))) :=
          mul_le_mul_of_nonneg_left h2 hq0
      _ = ((1 - 1 / n) / (1 - 1 / n + γ)) ^ (k + 1) * (α₀ - (1 + γ)) := by rw [pow_succ]; ring

/-- **Sil's-form iteration converges to `1 + γ`** (for `γ > 0`); at `γ = 1/n` this is the optimal sieve's
`1 + 1/n`. -/
theorem tendsto_silIter {n γ α₀ : ℝ} (hn : 1 < n) (hγ : 0 < γ) (h : 1 + γ ≤ α₀) :
    Tendsto (silIter n γ α₀) atTop (𝓝 (1 + γ)) := by
  have hn' : 1 / n < 1 := by
    rw [div_lt_one (by linarith)]
    exact hn
  set q := (1 - 1 / n) / (1 - 1 / n + γ) with hqdef
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one (by linarith)]
    linarith
  have hqk : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hlim : Tendsto (fun k : ℕ => (1 + γ) + q ^ k * (α₀ - (1 + γ))) atTop (𝓝 (1 + γ)) := by
    simpa using (hqk.mul_const (α₀ - (1 + γ))).const_add (1 + γ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim ?_ ?_
  · intro k
    exact (silIter_bounds hn hγ.le h k).1
  · intro k
    have h2 := (silIter_bounds hn hγ.le h k).2
    show silIter n γ α₀ k ≤ (1 + γ) + q ^ k * (α₀ - (1 + γ))
    linarith

end QRH.ArviKWall.OffSpike

#print axioms QRH.ArviKWall.OffSpike.tendsto_iter
#print axioms QRH.ArviKWall.OffSpike.balance
#print axioms QRH.ArviKWall.OffSpike.balance_ge
#print axioms QRH.ArviKWall.OffSpike.c_eq
#print axioms QRH.ArviKWall.OffSpike.step_lt
#print axioms QRH.ArviKWall.OffSpike.defaveri_step_sub
#print axioms QRH.ArviKWall.OffSpike.silStep_sil
#print axioms QRH.ArviKWall.OffSpike.silEnlargement_sil
#print axioms QRH.ArviKWall.OffSpike.sil_theta_eq
#print axioms QRH.ArviKWall.OffSpike.silBalance
#print axioms QRH.ArviKWall.OffSpike.one_le_silEnlargement
#print axioms QRH.ArviKWall.OffSpike.tendsto_silIter
