/-
The unmarked zero-density exponent as a lattice game (research/round9/README.md §1).

Rows of the sextic family with a zero at `Re = a`, `δ = ν = 2a − 1`, carry saturated witnesses
(7/8 paper, Prop. 8.3): for every `t ∈ [1, 3/2]` a Möbius block `M_r` and a plain block `S_m` with
`r ≤ t`, `r + m ≥ t`, `m ≤ 1/2`, `|M_r|² ≈ U^{νr}`, `|S_m|² ≈ U^{νm}`. The count exponents
(log_U of the number of rows) available for a saturated witness are
* `mcount ν y`: a Möbius-type block of length `y`, by the inverse moment (`y ≤ 1`, diagonal `U`)
  or by the sixth-power amplified long moment (`y ≥ 1`, `U^{(1+5y)/6}`);
* `pcount ν m`: a plain block of length `m ≤ 1/2`, by the plain fourth moment.

`rho ν = 1 − 10ν/(15 − 6ν)` is the exponent this gives (Xu–Sang's `(31 − 32σ)/(21 − 12σ)`).

* `count_ge_rho`, `count_at_tstar`: the defender's best detector length is `t* = 3s₀`,
  `s₀ = 5/(15 − 6ν)`, and the count there is exactly `rho`.
* `lattice_adversary`: the adversary whose saturated lengths form the lattice `s₀ℕ` (the two-term
  model `L ≈ 1 + bU^{−s₀(s − a)}`, `1/L ≈ Σ (−b)^k U^{−ks₀(s − a)}`) supplies a witness pair for
  every `t ∈ [1, 3/2]` (`lattice_pairs`), and every product witness `M^i S^j` has a length in
  `s₀ℕ`, whose count is at least `rho` (`lattice_counts_ge`). So no combination of the three
  inputs beats `rho`; only a better long line (or a new input) can.
* `rho_sens`: the exponent's sensitivity to the long line's intercept is `4ν/(5 − 2ν)`.
* `bootstrap_fails`: bounding the long moment row by row through the zero count,
  `max_δ′ ρ(δ′) + tδ′`, is worse than amplification `(1 + 5t)/6` at the corners `t = 231/200` and
  `t = 5/4` (witness `δ′ = 3/5`).
Status: proved.
-/
import Mathlib

namespace ZeroDensityGame

/-- Count exponent for a saturated Möbius-type block of length `y`. -/
noncomputable def mcount (ν y : ℝ) : ℝ := if y ≤ 1 then 1 - ν * y else 1 / 6 + (5 / 6 - ν) * y

/-- Count exponent for a saturated plain block of length `m` (fourth moment). -/
noncomputable def pcount (ν m : ℝ) : ℝ := 1 - 2 * ν * m

/-- The long line: the amplified long moment minus the saturation. -/
noncomputable def L (ν t : ℝ) : ℝ := 1 / 6 + (5 / 6 - ν) * t

/-- The best split count `max_r min(I(r), P(t − r)) = 1 − 2νt/3`. -/
noncomputable def short (ν t : ℝ) : ℝ := 1 - 2 * ν * t / 3

noncomputable def rho (ν : ℝ) : ℝ := 1 - 10 * ν / (15 - 6 * ν)

noncomputable def s0 (ν : ℝ) : ℝ := 5 / (15 - 6 * ν)

lemma den_pos {ν : ℝ} (hν : ν < 5 / 6) : 0 < 15 - 6 * ν := by linarith

/-- `rho` is the plain count at the lattice step, and the long line at three steps. -/
theorem rho_eq_plain {ν : ℝ} (_hν : ν < 5 / 6) : rho ν = pcount ν (s0 ν) := by
  unfold rho pcount s0; ring

theorem rho_eq_long {ν : ℝ} (hν : ν < 5 / 6) : rho ν = L ν (3 * s0 ν) := by
  have h : (15 - 6 * ν) ≠ 0 := (den_pos hν).ne'
  have hI : (15 - 6 * ν) * (15 - 6 * ν)⁻¹ = 1 := mul_inv_cancel₀ h
  unfold rho L s0
  simp only [div_eq_mul_inv]
  linear_combination (-5 / 6 : ℝ) * hI

theorem rho_eq_short {ν : ℝ} (_hν : ν < 5 / 6) : rho ν = short ν (3 * s0 ν) := by
  unfold rho short s0; ring

/-- The split count at any admissible `r` is at most `short`: a weighted mean of the two lines. -/
theorem split_le_short (ν t r : ℝ) :
    min (1 - ν * r) (pcount ν (t - r)) ≤ short ν t := by
  unfold pcount short
  have : min (1 - ν * r) (1 - 2 * ν * (t - r)) ≤
      2 / 3 * (1 - ν * r) + 1 / 3 * (1 - 2 * ν * (t - r)) := by
    rcases le_total (1 - ν * r) (1 - 2 * ν * (t - r)) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  linarith

/-- The split count attains `short` at `r = 2t/3`. -/
theorem split_at_two_thirds (ν t : ℝ) :
    min (1 - ν * (2 * t / 3)) (pcount ν (t - 2 * t / 3)) = short ν t := by
  unfold pcount short
  have : 1 - ν * (2 * t / 3) = 1 - 2 * ν * (t - 2 * t / 3) := by ring
  rw [this, min_self]; ring

/-- For every detector length the count is at least `rho`. -/
theorem count_ge_rho {ν t : ℝ} (hν0 : 0 ≤ ν) (hν : ν < 5 / 6) :
    rho ν ≤ max (L ν t) (short ν t) := by
  have h := den_pos hν
  rcases le_total t (3 * s0 ν) with ht | ht
  · apply le_max_of_le_right
    rw [rho_eq_short hν]
    unfold short
    nlinarith
  · apply le_max_of_le_left
    rw [rho_eq_long hν]
    unfold L
    have h56 : 0 ≤ 5 / 6 - ν := by linarith
    nlinarith [mul_le_mul_of_nonneg_left ht h56]

/-- At `t* = 3s₀` the count is exactly `rho`. -/
theorem count_at_tstar {ν : ℝ} (hν : ν < 5 / 6) :
    max (L ν (3 * s0 ν)) (short ν (3 * s0 ν)) = rho ν := by
  rw [← rho_eq_long hν, ← rho_eq_short hν, max_self]

/-- `t*` lies in the detector range `[1, 3/2]`. -/
theorem tstar_range {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν ≤ 5 / 6) :
    1 ≤ 3 * s0 ν ∧ 3 * s0 ν ≤ 3 / 2 := by
  have h : 0 < 15 - 6 * ν := by linarith
  unfold s0
  constructor
  · rw [mul_div_assoc', le_div_iff₀ h]; linarith
  · rw [mul_div_assoc', div_le_iff₀ h]; linarith

/-- The lattice step is at most `1/2`, and two steps fit below `1`, three reach above it. -/
theorem s0_bounds {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν ≤ 5 / 6) :
    0 < s0 ν ∧ s0 ν ≤ 1 / 2 ∧ 2 * s0 ν ≤ 1 ∧ 1 ≤ 3 * s0 ν := by
  have h : 0 < 15 - 6 * ν := by linarith
  refine ⟨div_pos (by norm_num) h, ?_, ?_, (tstar_range hν0 hν).1⟩
  · unfold s0; rw [div_le_iff₀ h]; linarith
  · unfold s0; rw [mul_div_assoc', div_le_iff₀ h]; linarith

/-- **The lattice adversary supplies a saturated pair for every detector length** `t ∈ [1, 3/2]`
(for `ν ≥ 5/18`): `(2s₀, s₀)` below `t* = 3s₀`, `(3s₀, s₀)` above it. Both satisfy Prop. 8.3's
constraints `r ≤ t`, `r + m ≥ t`, `t − 1/2 ≤ r`, `m ≤ 1/2`. -/
theorem lattice_pairs {ν t : ℝ} (hν0 : 5 / 18 ≤ ν) (hν : ν ≤ 5 / 6) (ht1 : 1 ≤ t)
    (ht2 : t ≤ 3 / 2) :
    ∃ i : ℕ, (i = 2 ∨ i = 3) ∧ i * s0 ν ≤ t ∧ t ≤ i * s0 ν + s0 ν ∧ t - 1 / 2 ≤ i * s0 ν := by
  have h : 0 < 15 - 6 * ν := by linarith
  obtain ⟨hs, hs2, -, h3⟩ := s0_bounds (by linarith) hν
  rcases le_total t (3 * s0 ν) with ht | ht
  · refine ⟨2, Or.inl rfl, ?_, ?_, ?_⟩ <;> push_cast <;> [linarith; linarith; linarith]
  · refine ⟨3, Or.inr rfl, ?_, ?_, ?_⟩ <;> push_cast
    · linarith
    · -- four steps reach `3/2`
      have : 3 / 2 ≤ 4 * s0 ν := by
        unfold s0; rw [mul_div_assoc', le_div_iff₀ h]; linarith
      linarith
    · linarith

/-- **Every lattice length counts at least `rho`.** The products `M^i S^j` of the adversary's
witnesses have lengths `k s₀`; the defender's best count for each is `mcount` (Möbius-type, any
length) or `pcount` (plain, only `k = 1` is admissible since `2s₀ > 1/2` unless `ν = 5/6`). -/
theorem lattice_counts_ge {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν < 5 / 6) (k : ℕ) (hk : 1 ≤ k) :
    rho ν ≤ mcount ν (k * s0 ν) := by
  have h := den_pos hν
  obtain ⟨hs, hs2, h2, h3⟩ := s0_bounds hν0 hν.le
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold mcount
  split_ifs with hy
  · -- `k s₀ ≤ 1`: the diagonal count; `k ≤ 2` unless `3s₀ = 1`, which forces `ν = 0`
    rw [rho_eq_plain hν]
    unfold pcount
    rcases le_or_gt (k : ℝ) 2 with hk2 | hk2
    · nlinarith [mul_nonneg (mul_nonneg hν0 hs.le) (by linarith : (0 : ℝ) ≤ 2 - k)]
    · have hk3 : (3 : ℝ) ≤ k := by
        have : (2 : ℕ) < k := by exact_mod_cast hk2
        exact_mod_cast this
      have h3eq : 3 * s0 ν = 1 := le_antisymm (by nlinarith) h3
      have hν' : ν = 0 := by
        unfold s0 at h3eq
        rw [mul_div_assoc', div_eq_iff h.ne'] at h3eq
        linarith
      subst hν'
      norm_num
  · push Not at hy
    -- `k s₀ > 1 ≥ 2s₀` forces `k ≥ 3`: the long line is above its value at `t* = 3s₀`
    have hk3 : (3 : ℝ) ≤ k := by
      by_contra hc
      push Not at hc
      have : k < 3 := by exact_mod_cast hc
      have : (k : ℝ) ≤ 2 := by
        have : k ≤ 2 := by omega
        exact_mod_cast this
      nlinarith
    rw [rho_eq_long hν]
    unfold L
    have h56 : 0 ≤ 5 / 6 - ν := by linarith
    have h3k : 3 * s0 ν ≤ k * s0 ν := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3k h56]

/-- The plain witness of the adversary has length `s₀ ≤ 1/2` and counts exactly `rho`. -/
theorem lattice_plain {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν < 5 / 6) :
    s0 ν ≤ 1 / 2 ∧ pcount ν (s0 ν) = rho ν :=
  ⟨(s0_bounds hν0 hν.le).2.1, (rho_eq_plain hν).symm⟩

/-- **Sensitivity to the long line.** Lowering the long line's intercept by `ε` (the long moment
exponent `(1 + 5t)/6 − ε`) lowers the game value by `ε · 4ν/(5 − 2ν)`: the crossing of
`L − ε` with `short` moves to `t = (5 + 6ε)/(5 − 2ν)`. -/
theorem rho_sens {ν ε : ℝ} (hν : ν < 5 / 6) :
    let t := (5 + 6 * ε) / (5 - 2 * ν)
    L ν t - ε = short ν t ∧ short ν t = rho ν - ε * (4 * ν / (5 - 2 * ν)) := by
  intro t
  have h1 : (5 - 2 * ν) ≠ 0 := by linarith
  have h2 : (15 - 6 * ν) ≠ 0 := by linarith
  have hJ : (5 - 2 * ν) * (5 - 2 * ν)⁻¹ = 1 := mul_inv_cancel₀ h1
  have hI : (15 - 6 * ν) * (15 - 6 * ν)⁻¹ = 1 := mul_inv_cancel₀ h2
  constructor
  · simp only [t, L, short, div_eq_mul_inv]
    linear_combination ((5 + 6 * ε) / 6) * hJ
  · simp only [t, short, rho, div_eq_mul_inv]
    linear_combination (-10 * ν * (15 - 6 * ν)⁻¹) * hJ + (10 * ν / 3 * (5 - 2 * ν)⁻¹) * hI

/-- **The bootstrap fails.** Feeding the zero count back into the long moment
(`Σ_u |M_u(U^t)|² ≤ Σ_{δ′} U^{ρ(δ′) + tδ′}`) is worse than sixth-power amplification at the count's
corners: already the bin `δ′ = 3/5` exceeds `(1 + 5t)/6`. -/
theorem bootstrap_fails :
    (1 + 5 * (231 / 200 : ℝ)) / 6 < rho (3 / 5) + (231 / 200) * (3 / 5) ∧
    (1 + 5 * (5 / 4 : ℝ)) / 6 < rho (3 / 5) + (5 / 4) * (3 / 5) := by
  unfold rho; constructor <;> norm_num


/-! ### Round 10: pieces of `μ·log = −Λ∗μ` (`../round10/README.md` §1)

On squarefree `n`, `μ(n) log n = −Σ_{p|n} log p · μ(n/p)`, so the long witness `M(U^t)` splits
into pieces `Q(U^p)·M(U^{t−p})`. On bin rows the prime block is bounded pointwise by the amplitude
cap `|Q|² ≤ P^{1+ν}` (7/8 Lemma 19.1). The Möbius block gets the inverse moment when `t − p ≤ 1`
(`pieceShort`) and amplification when `t − p ≥ 1` (`pieceLong`). -/

/-- Count exponent of a piece whose Möbius block has length `t − p ≤ 1`. -/
noncomputable def pieceShort (ν t p : ℝ) : ℝ := 1 - t * ν + p * ν

/-- Count exponent of a piece whose Möbius block has length `t − p ≥ 1` (amplified). -/
noncomputable def pieceLong (ν t p : ℝ) : ℝ := L ν t - (5 / 6 - ν) * p

/-- At the adversary's own length `t = 3s₀`, a piece with a short Möbius block beats the long
line exactly when its prime block is shorter than `s₀`. -/
theorem piece_threshold {ν p : ℝ} (hν0 : 0 < ν) (hν : ν < 5 / 6) :
    pieceShort ν (3 * s0 ν) p < L ν (3 * s0 ν) ↔ p < s0 ν := by
  rw [← rho_eq_long hν, rho_eq_plain hν]
  unfold pieceShort pcount
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hν0.le]
  · intro h
    nlinarith [mul_lt_mul_of_pos_left h hν0]

/-- The adversary's first piece, prime block at `s₀` and Möbius block at `2s₀`, counts exactly `ρ`. -/
theorem piece_at_s0 {ν : ℝ} (hν : ν < 5 / 6) : pieceShort ν (3 * s0 ν) (s0 ν) = rho ν := by
  rw [rho_eq_plain hν]; unfold pieceShort pcount; ring

/-- With an amplified Möbius block, every piece with a prime factor of positive length beats the
long line. -/
theorem pieceLong_lt {ν t p : ℝ} (hν : ν < 5 / 6) (hp : 0 < p) : pieceLong ν t p < L ν t := by
  unfold pieceLong
  have : 0 < (5 / 6 - ν) * p := mul_pos (by linarith) hp
  linarith

/-- At `t = 3s₀` the inverse-moment regime `p ≥ t − 1` starts below `s₀` (because `2s₀ < 1`),
so every prime length in `(0, s₀)` gives a piece below the long line. -/
theorem regimes_meet_below_s0 {ν : ℝ} (hν : ν < 5 / 6) : 3 * s0 ν - 1 < s0 ν := by
  have h := den_pos hν
  have hs : s0 ν * (15 - 6 * ν) = 5 := by unfold s0; field_simp
  have hpos : 0 < s0 ν := by unfold s0; positivity
  nlinarith

/-- **Amplification is the 11/12 strip on the excess length**:
`(1 + 5t)/6 = 1 + (t − 1)(2·(11/12) − 1)`. -/
theorem amplification_is_eleven_twelfths (t : ℝ) :
    (1 + 5 * t) / 6 = 1 + (t - 1) * (2 * (11 / 12) - 1) := by ring

/-- The dual asymptotic needed to beat amplification at length `t`: a relative error
`(D²/U)^{−η}` beats `U^{1/6}D^{5/6}` iff `η ≥ (t − 1)/(6(2t − 1))` (exponents in `log U`). -/
theorem dual_asymptotic_threshold {t η : ℝ} (ht : 1 < t) :
    t * (1 - 2 * η) + η ≤ (1 + 5 * t) / 6 ↔ (t - 1) / (6 * (2 * t - 1)) ≤ η := by
  have h : 0 < 6 * (2 * t - 1) := by linarith
  rw [div_le_iff₀ h]
  constructor <;> intro h' <;> nlinarith

end ZeroDensityGame
