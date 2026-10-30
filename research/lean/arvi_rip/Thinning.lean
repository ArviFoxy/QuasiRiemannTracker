import Mathlib

/-!
# Random row thinning is energy-neutral (research file, RIP program: randomized dictionaries)

Rows `z ∈ W` are kept independently with probability `ρ` (Bernoulli weights over subsets, no measure theory).
* `thin_avg`: the average energy over thinnings is exactly `ρ` times the energy on `W`.
* `avg_bound_ge`: if `N S` dominates the energy on each thinning `S`, its average is at least `ρ · energy(W)`
  (so no randomization of the rows dilutes the energy on a *fixed* `W` on average).
* `thinning_pays_back`: a `ρ`-diluted bound `ρX + Y` on every thinning gives only `X + Y/ρ` on `W`.
* `closure_payback`: in the K-wall closure, diluting the sextic excess by `δ₀` through thinning is paid back:
  `max(1, 7/6 − δ₀) + δ₀ ≥ 7/6`.
These are the facts behind "randomizing the sextic dictionary is Jensen-neutral" (journal, RIP (3)).
-/

namespace QRH.ArviRIP

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Bernoulli(`ρ`) weight of a subset `S` of `W`. -/
def bern (ρ : ℝ) (W S : Finset ι) : ℝ := ρ ^ S.card * (1 - ρ) ^ (W.card - S.card)

omit [DecidableEq ι] in
theorem bern_total (ρ : ℝ) (W : Finset ι) : ∑ S ∈ W.powerset, bern ρ W S = 1 := by
  unfold bern; rw [Finset.sum_pow_mul_eq_add_pow]; simp

omit [DecidableEq ι] in
theorem bern_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (W S : Finset ι) : 0 ≤ bern ρ W S :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

/-- Each row is kept with probability `ρ`. -/
theorem bern_mem (ρ : ℝ) {W : Finset ι} {z : ι} (hz : z ∈ W) :
    ∑ S ∈ W.powerset, (if z ∈ S then bern ρ W S else 0) = ρ := by
  obtain ⟨W', hW'⟩ : ∃ W', W' = W.erase z := ⟨_, rfl⟩
  have hW : W = insert z W' := hW' ▸ (Finset.insert_erase hz).symm
  have hz' : z ∉ W' := hW' ▸ Finset.notMem_erase z W
  rw [hW, Finset.sum_powerset_insert hz']
  have h1 : ∑ S ∈ W'.powerset, (if z ∈ S then bern ρ (insert z W') S else 0) = 0 := by
    refine Finset.sum_eq_zero (fun S hS => ?_)
    have : z ∉ S := fun h => hz' (Finset.mem_powerset.mp hS h)
    simp [this]
  have h2 : ∀ T ∈ W'.powerset, (if z ∈ insert z T then bern ρ (insert z W') (insert z T) else 0) =
      ρ * bern ρ W' T := by
    intro T hT
    have hzT : z ∉ T := fun h => hz' (Finset.mem_powerset.mp hT h)
    simp only [Finset.mem_insert_self, ite_true, bern]
    rw [Finset.card_insert_of_notMem hz', Finset.card_insert_of_notMem hzT, Nat.add_sub_add_right,
      pow_succ]
    ring
  rw [h1, zero_add, Finset.sum_congr rfl h2, ← Finset.mul_sum, bern_total, mul_one]

/-- **Average energy over thinnings.** -/
theorem thin_avg (ρ : ℝ) (W : Finset ι) (f : ι → ℝ) :
    ∑ S ∈ W.powerset, bern ρ W S * ∑ z ∈ S, f z = ρ * ∑ z ∈ W, f z := by
  have hS : ∀ S ∈ W.powerset, bern ρ W S * ∑ z ∈ S, f z =
      ∑ z ∈ W, f z * (if z ∈ S then bern ρ W S else 0) := by
    intro S hS
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hS), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => mul_comm _ _)
  rw [Finset.sum_congr rfl hS, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [← Finset.mul_sum, bern_mem ρ hz, mul_comm]

/-- **No free dilution on average.** -/
theorem avg_bound_ge {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (W : Finset ι) (f : ι → ℝ)
    (N : Finset ι → ℝ) (hN : ∀ S ⊆ W, ∑ z ∈ S, f z ≤ N S) :
    ρ * ∑ z ∈ W, f z ≤ ∑ S ∈ W.powerset, bern ρ W S * N S := by
  rw [← thin_avg]
  exact Finset.sum_le_sum (fun S hS =>
    mul_le_mul_of_nonneg_left (hN S (Finset.mem_powerset.mp hS)) (bern_nonneg h0 h1 W S))

/-- **Thinning pays back its dilution.** -/
theorem thinning_pays_back {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) (W : Finset ι) (f : ι → ℝ)
    (X Y : ℝ) (h : ∀ S ⊆ W, ∑ z ∈ S, f z ≤ ρ * X + Y) : ∑ z ∈ W, f z ≤ X + Y / ρ := by
  have key : ρ * ∑ z ∈ W, f z ≤ ρ * X + Y := by
    have := avg_bound_ge h0.le h1 W f (fun _ => ρ * X + Y) h
    rwa [← Finset.sum_mul, bern_total, one_mul] at this
  have h2 : ∑ z ∈ W, f z ≤ (ρ * X + Y) / ρ := by
    rw [le_div_iff₀ h0]; linarith
  calc ∑ z ∈ W, f z ≤ (ρ * X + Y) / ρ := h2
    _ = X + Y / ρ := by field_simp

/-- **The K-wall closure pays back a thinning dilution `δ₀` exactly.** -/
theorem closure_payback (δ₀ : ℝ) : (7 : ℝ) / 6 ≤ max 1 (7 / 6 - δ₀) + δ₀ := by
  have := le_max_right (1 : ℝ) (7 / 6 - δ₀)
  linarith

end QRH.ArviRIP

#print axioms QRH.ArviRIP.thin_avg
#print axioms QRH.ArviRIP.thinning_pays_back
