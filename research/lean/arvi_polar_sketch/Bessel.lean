/-
SKETCH package (see `Polar.lean`). This file has no `sorry`, and nothing here depends on `sorryAx`: the polar input
enters as the hypothesis `PolarInput`, which the sorry'd `polarInput` would supply.

The K-wall's source-spike term for Mellin-zero vectors. The corrected sieve weights the twist-`m` spike by its strength
`w_m ≤ (B / N m)^{1/q}` (the multiplicity of the Poisson copies). With Lindelöf on average in the twist aspect, a
dyadic decomposition in `N m` gives

  `Σ_{m ∈ twistBox M} w_m |⟨v, f_m⟩|² ≤ C X^{1+ε} 2^{1+ε} (log₂ M + 1) B^{1/q} M^{1 + ε − 1/q}`

(`weighted_dyadic`, pure analysis), and `weighted_bessel` applies it to the polar input. At the K-wall
(`M = B^{1−qγ}`, `X ≈ B`, `q = 6`) the right side is `B^{1+1/6} M^{5/6} B^{O(ε)} = B^{2−5γ+O(ε)}`, against the diagonal
`B^{1+γ} ‖v‖² ≈ B^{2+γ}`: smaller by `B^{−6γ+O(ε)}`.
-/
import Submissions.arvi_polar_sketch.Polar

set_option autoImplicit false
namespace QRH.ArviPolarSketch
noncomputable section
open scoped BigOperators
open OAI QRH.ArviKWall.BalancedSieve

/-! ### Twist norms and twist boxes -/

theorem four_twistNorm (p : ℤ × ℤ) : 4 * twistNorm p = (2 * p.1 - p.2) ^ 2 + 3 * p.2 ^ 2 := by
  unfold twistNorm; ring

theorem four_twistNorm' (p : ℤ × ℤ) : 4 * twistNorm p = (2 * p.2 - p.1) ^ 2 + 3 * p.1 ^ 2 := by
  unfold twistNorm; ring

theorem twistNorm_pos {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < twistNorm p := by
  have h := four_twistNorm p
  by_contra hle
  push Not at hle
  have h1 : p.2 = 0 := by nlinarith [sq_nonneg (2 * p.1 - p.2), sq_nonneg p.2]
  have h2 : p.1 = 0 := by
    have h3 : (2 * p.1 - p.2) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * p.1 - p.2), sq_nonneg p.2]
    rw [h1] at h3
    nlinarith [h3]
  exact hp (Prod.ext h2 h1)

theorem mem_twistBox_iff {M : ℕ} {p : ℤ × ℤ} :
    p ∈ twistBox M ↔ (p.1 ∈ Finset.Icc (-(M : ℤ)) M ∧ p.2 ∈ Finset.Icc (-(M : ℤ)) M) ∧ p ≠ 0 ∧ twistNorm p ≤ M := by
  unfold twistBox
  simp only [Finset.mem_filter, Finset.mem_product]

/-- A twist of norm `≤ m` (`m ≥ 2`) lies in `twistBox m`: its coordinates are at most `√(4m/3) ≤ m`. -/
theorem mem_twistBox_of_norm_le {p : ℤ × ℤ} (hp : p ≠ 0) {m : ℕ} (hm : 2 ≤ m) (hN : twistNorm p ≤ m) :
    p ∈ twistBox m := by
  rw [mem_twistBox_iff]
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have h1 := four_twistNorm p
  have h2 := four_twistNorm' p
  have hy : p.2 ^ 2 ≤ (m : ℤ) ^ 2 := by nlinarith [sq_nonneg (2 * p.1 - p.2)]
  have hx : p.1 ^ 2 ≤ (m : ℤ) ^ 2 := by nlinarith [sq_nonneg (2 * p.2 - p.1)]
  have hm0 : (0 : ℤ) ≤ m := by omega
  refine ⟨⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩, hp, hN⟩
  · nlinarith [sq_nonneg (p.1 + m)]
  · nlinarith [sq_nonneg (p.1 - m)]
  · nlinarith [sq_nonneg (p.2 + m)]
  · nlinarith [sq_nonneg (p.2 - m)]

/-- The dyadic shell of a twist: `⌊log₂ N m⌋`. -/
def shell (p : ℤ × ℤ) : ℕ := Nat.log 2 (twistNorm p).toNat

theorem shell_bounds {p : ℤ × ℤ} (hp : p ≠ 0) :
    (2 : ℝ) ^ shell p ≤ (twistNorm p : ℝ) ∧ (twistNorm p : ℝ) < 2 ^ (shell p + 1) := by
  have hpos := twistNorm_pos hp
  have hne : (twistNorm p).toNat ≠ 0 := by omega
  have hcast : ((twistNorm p).toNat : ℝ) = (twistNorm p : ℝ) := by
    have : ((twistNorm p).toNat : ℤ) = twistNorm p := Int.toNat_of_nonneg hpos.le
    exact_mod_cast this
  have h1 := Nat.pow_log_le_self 2 hne
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (twistNorm p).toNat
  rw [← hcast]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ### The dyadic estimate -/

/-- `(B/u)^{1/q} (2uX)^{1+ε} = B^{1/q} 2^{1+ε} X^{1+ε} u^{1+ε−1/q}`. -/
theorem shell_factor {B u X ε r : ℝ} (hB : 0 < B) (hu : 0 < u) (hX : 0 < X) :
    (B / u) ^ r * (2 * u * X) ^ (1 + ε) = B ^ r * 2 ^ (1 + ε) * X ^ (1 + ε) * u ^ (1 + ε - r) := by
  rw [Real.div_rpow hB.le hu.le, Real.mul_rpow (by positivity) hX.le, Real.mul_rpow (by norm_num) hu.le,
    Real.rpow_sub hu]
  field_simp

/-- **The weighted dyadic estimate.** Nonnegative twist data `a` with the mean value `Σ_{twistBox M'} a ≤ C (M' X)^{1+ε}`
at every scale, and weights `w_m ≤ (B / N m)^{1/q}`, give
`Σ_{twistBox M} w a ≤ C X^{1+ε} 2^{1+ε} (log₂ M + 1) B^{1/q} M^{1+ε−1/q}`. -/
theorem weighted_dyadic {a w : ℤ × ℤ → ℝ} {C X B ε : ℝ} {q : ℕ} (hq : 1 ≤ q) (hC : 0 ≤ C) (hX : 1 ≤ X)
    (hB : 0 < B) (hε : 0 ≤ ε) (ha : ∀ p, 0 ≤ a p)
    (hmv : ∀ M' : ℕ, 2 ≤ M' → ∑ p ∈ twistBox M', a p ≤ C * ((M' : ℝ) * X) ^ (1 + ε))
    (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ p ∈ twistBox M, w p ≤ (B / (twistNorm p : ℝ)) ^ (1 / (q : ℝ))) :
    ∑ p ∈ twistBox M, w p * a p ≤
      ((Nat.log 2 M + 1 : ℕ) : ℝ) *
        (C * (B ^ (1 / (q : ℝ)) * 2 ^ (1 + ε) * X ^ (1 + ε) * (M : ℝ) ^ (1 + ε - 1 / (q : ℝ)))) := by
  set J := Nat.log 2 M with hJ
  set r : ℝ := 1 / (q : ℝ) with hr
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one (by linarith)]; exact hq'
  have hexp : 0 ≤ 1 + ε - r := by linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- every twist of the box lies in a shell `j ≤ J`
  have hmaps : ∀ p ∈ twistBox M, shell p ∈ Finset.range (J + 1) := by
    intro p hp
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hN := (mem_twistBox_iff.mp hp).2.2
    exact Nat.log_mono_right (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- the bound for one shell
  have hshell : ∀ j ∈ Finset.range (J + 1),
      ∑ p ∈ (twistBox M).filter (fun p => shell p = j), w p * a p ≤
        C * (B ^ r * 2 ^ (1 + ε) * X ^ (1 + ε) * (M : ℝ) ^ (1 + ε - r)) := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    set u : ℝ := (2 : ℝ) ^ j with hu
    have hu0 : 0 < u := by positivity
    have huM : u ≤ M := by
      have h2 : 2 ^ J ≤ M := Nat.pow_log_le_self 2 (by omega)
      have h3 : (2 : ℕ) ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hjJ
      rw [hu]; exact_mod_cast h3.trans h2
    -- weights on the shell
    have hwj : ∀ p ∈ (twistBox M).filter (fun p => shell p = j), w p ≤ (B / u) ^ r := by
      intro p hp
      obtain ⟨hpM, hsh⟩ := Finset.mem_filter.mp hp
      have hp0 := (mem_twistBox_iff.mp hpM).2.1
      have hb := (shell_bounds hp0).1
      rw [hsh] at hb
      refine (hw p hpM).trans ?_
      have htn : (0 : ℝ) < (twistNorm p : ℝ) := by exact_mod_cast twistNorm_pos hp0
      apply Real.rpow_le_rpow (div_nonneg hB.le htn.le) _ hr0
      exact div_le_div_of_nonneg_left hB.le hu0 hb
    -- the shell lies in `twistBox (2^{j+1})`
    have hsub : (twistBox M).filter (fun p => shell p = j) ⊆ twistBox (2 ^ (j + 1)) := by
      intro p hp
      obtain ⟨hpM, hsh⟩ := Finset.mem_filter.mp hp
      have hp0 := (mem_twistBox_iff.mp hpM).2.1
      have hb := (shell_bounds hp0).2
      rw [hsh] at hb
      have hb' : twistNorm p ≤ ((2 ^ (j + 1) : ℕ) : ℤ) := by
        have : (twistNorm p : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by push_cast; exact hb
        have := this.le
        exact_mod_cast this
      exact mem_twistBox_of_norm_le hp0 (by
        have : 2 ^ 1 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using this) hb'
    have hmvj := hmv (2 ^ (j + 1)) (by
      have : 2 ^ 1 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this)
    calc ∑ p ∈ (twistBox M).filter (fun p => shell p = j), w p * a p
        ≤ ∑ p ∈ (twistBox M).filter (fun p => shell p = j), (B / u) ^ r * a p :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hwj p hp) (ha p)
      _ = (B / u) ^ r * ∑ p ∈ (twistBox M).filter (fun p => shell p = j), a p := by rw [Finset.mul_sum]
      _ ≤ (B / u) ^ r * ∑ p ∈ twistBox (2 ^ (j + 1)), a p := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => ha p
      _ ≤ (B / u) ^ r * (C * (((2 ^ (j + 1) : ℕ) : ℝ) * X) ^ (1 + ε)) :=
          mul_le_mul_of_nonneg_left hmvj (by positivity)
      _ = C * ((B / u) ^ r * (2 * u * X) ^ (1 + ε)) := by
          have e : (((2 ^ (j + 1) : ℕ) : ℝ) * X) = 2 * u * X := by rw [hu]; push_cast; ring
          rw [e]; ring
      _ = C * (B ^ r * 2 ^ (1 + ε) * X ^ (1 + ε) * u ^ (1 + ε - r)) := by
          rw [shell_factor hB hu0 hX0]
      _ ≤ C * (B ^ r * 2 ^ (1 + ε) * X ^ (1 + ε) * (M : ℝ) ^ (1 + ε - r)) := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow hu0.le huM hexp
  calc ∑ j ∈ Finset.range (J + 1), ∑ p ∈ (twistBox M).filter (fun p => shell p = j), w p * a p
      ≤ ∑ _j ∈ Finset.range (J + 1), C * (B ^ r * 2 ^ (1 + ε) * X ^ (1 + ε) * (M : ℝ) ^ (1 + ε - r)) :=
        Finset.sum_le_sum hshell
    _ = ((J + 1 : ℕ) : ℝ) * (C * (B ^ r * 2 ^ (1 + ε) * X ^ (1 + ε) * (M : ℝ) ^ (1 + ε - r))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The source-spike term of a Mellin-zero vector** (uses `polarInput` through `hP`). With spike strengths
`w_m ≤ (B / N m)^{1/q}`, `Σ_{twistBox M} w_m |⟨v, f_m⟩|² ≪ (log₂ M + 1) B^{1/q} M^{1+ε−1/q} X^{1+ε}`. -/
theorem weighted_bessel {k q : ℕ} {W : ℝ → ℂ} {v₁ ε : ℝ} (hq : 1 ≤ q) (hε : 0 ≤ ε)
    (hP : PolarInput k q W v₁ ε) (h0 : mellin W (pole q) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B X : ℝ) (M : ℕ), 0 < B → 1 ≤ X → 1 ≤ M → ∀ w : ℤ × ℤ → ℝ,
      (∀ p ∈ twistBox M, w p ≤ (B / (twistNorm p : ℝ)) ^ (1 / (q : ℝ))) →
      ∑ p ∈ twistBox M, w p * ‖thetaCorr k W v₁ X p‖ ^ 2 ≤
        ((Nat.log 2 M + 1 : ℕ) : ℝ) *
          (C * (B ^ (1 / (q : ℝ)) * 2 ^ (1 + ε) * X ^ (1 + ε) * (M : ℝ) ^ (1 + ε - 1 / (q : ℝ)))) := by
  obtain ⟨C, A, hC, -, -, hmv⟩ := mellin_zero_bounds hP h0
  refine ⟨C, hC, fun B X M hB hX hM w hw => ?_⟩
  exact weighted_dyadic hq hC.le hX hB hε (fun p => sq_nonneg _) (fun M' _ => hmv M' X hX) M hM hw

end
end QRH.ArviPolarSketch

#print axioms QRH.ArviPolarSketch.weighted_dyadic
#print axioms QRH.ArviPolarSketch.weighted_bessel
