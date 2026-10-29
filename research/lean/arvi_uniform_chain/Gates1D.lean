/- The one-variable gates of a marked density-split step, proved once for all real parameters.

`hybridGatesM_of_scalar` produces `QRH.ArviDensity.HybridGatesM qf B0 L0 c0 B L c A D` from

* the standing facts `0 < A`, `0 < D`, `L < L0`, `0 < L0`, `0 < 6 B0 - L0`, `0 < vmax`
  (`vmax = c - cross B0 L0 B L`, `s0 = cross B0 L0 B L`);
* a few explicit scalar inequalities, each an endpoint value of a gate (at `v = 0` or at
  `v = vmax`), stated with the definitions `dens`, `sel`, `cross`, `gRetainedCap`, `gRefUpper`
  of `Source.HybridGates`, so that they are closed by `norm_num [dens, sel, cross, ...]` on
  rational parameters;
* the one remaining field `high_marked`, taken verbatim as a hypothesis `hhigh`.

How each field is obtained (`u(v) = sel A D v = A v/(1+D v)`, `q(v) = dens B0 L0 L A D v`):

* `sel_den_pos`, `dens_den_pos`, `low_identity`, `low_div_eq`, `sel_hasDerivAt`: from `D ≥ 0`,
  `L < L0`, `0 < 6 B0 - L0`, `0 < A` and the cleared identities of `Source.HybridGates`;
* `q_lower`, `q_floor`, `q_upper`: `q` is nonincreasing (its denominator increases), so the reserves
  are `q(vmax) - 1/2`, `q(vmax) - qf`, `3/4 - q(0)`;
* `H_lower`, `reference_upper_positive`: nonincreasing in `v` (`u` is nondecreasing), reserve = the
  value at `vmax`;
* `low_per_excess_width`, `selection_monotonicity`: `(1/1000) L0 A/(1+D v)` and `A/(1+D v)^2` are
  nonincreasing, reserve = the (automatically positive) value at `vmax`;
* `retained_cap`, `retained_width`, `principal_reference`, `second_reference`, `second_diagonal`:
  every one of these gates has the shape `α + β v - γ u(v)` (see `Gates1D.gRetainedCap_eq`, ...).
  The cleared form `(α + β v - γ u(v)) (1 + D v) = α + b v + a v^2` with `a = β D`,
  `b = α D + β - γ A` is a quadratic, and `ShapePos` is exactly the condition that this quadratic
  is positive on `[0, vmax]`: `α > 0`, the value at `vmax` is positive, and the quadratic is concave
  (`β ≤ 0`), or nondecreasing (`b ≥ 0`), or has no real root (`b^2 < 4 a α`), or is nonincreasing on
  `[0, vmax]` (`2 a vmax ≤ -b`).  One generic lemma (`Gates1D.shape_unifPos`) covers all five gates.

Remark.  The tempting "two linear pieces" bound `u(v) ≤ min (A v) (A/D)` is too lossy at the end of
the chain (it fails for the principal reference gate of steps 128 and 129, where `D vmax < 1`);
the quadratic criterion `ShapePos` is exact and avoids it. -/
import Submissions.arvi_density.Source.HybridGatesMarked

set_option autoImplicit false
namespace QRH.ArviUniformChain

open QRH.ArviDensity QRH.ArviDensity.Hybrid

/-- Positivity of the gate `v ↦ α + β v - γ · sel A D v` on `[0, T]`, as scalar data:
`α > 0`, the cleared value at `T` is positive, and the cleared quadratic
`α + b v + a v²` (`a = β D`, `b = α D + β - γ A`) has no zero on `[0, T]` for one of the four
elementary reasons (concave, nondecreasing, no real root, nonincreasing on `[0, T]`). -/
def ShapePos (A D α β γ T : ℝ) : Prop :=
  0 < α ∧ 0 < (α + β * T) * (1 + D * T) - γ * A * T ∧
    (β ≤ 0 ∨ 0 ≤ α * D + β - γ * A ∨ (α * D + β - γ * A) ^ 2 < 4 * (β * D) * α ∨
      2 * (β * D) * T ≤ -(α * D + β - γ * A))

namespace Gates1D

/-! ### Elementary facts on `sel` and `dens` -/

theorem one_add_pos {D v : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) : 0 < 1 + D * v := by
  have := mul_nonneg hD hv
  linarith

theorem sel_nonneg {A D v : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hv : 0 ≤ v) : 0 ≤ sel A D v :=
  div_nonneg (mul_nonneg hA hv) (one_add_pos hD hv).le

/-- `u(v) = A v/(1+D v)` is nondecreasing on `v ≥ 0`. -/
theorem sel_mono {A D v w : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hv : 0 ≤ v) (hvw : v ≤ w) :
    sel A D v ≤ sel A D w := by
  have hw : 0 ≤ w := hv.trans hvw
  unfold sel
  rw [div_le_div_iff₀ (one_add_pos hD hv) (one_add_pos hD hw)]
  nlinarith [mul_nonneg hA (sub_nonneg.2 hvw)]

theorem densE_pos {B0 L0 L A D v : ℝ} (hLL : L < L0) (h6 : 0 < 6 * B0 - L0) (hA : 0 < A)
    (hD : 0 ≤ D) (hv : 0 ≤ v) : 0 < densE B0 L0 L A D v := by
  unfold densE
  have h1 : 0 < (L0 - L) * (1 + D * v) := mul_pos (sub_pos.2 hLL) (one_add_pos hD hv)
  have h2 : 0 < (6 * B0 - L0) * A := mul_pos h6 hA
  linarith

/-- `q(v)` is nonincreasing on `v ≥ 0`. -/
theorem dens_antitone {B0 L0 L A D v w : ℝ} (hLL : L < L0) (h6 : 0 < 6 * B0 - L0) (hL0 : 0 < L0)
    (hA : 0 < A) (hD : 0 ≤ D) (hv : 0 ≤ v) (hvw : v ≤ w) :
    dens B0 L0 L A D w ≤ dens B0 L0 L A D v := by
  have hw : 0 ≤ w := hv.trans hvw
  have hEv := densE_pos hLL h6 hA hD hv
  have hK : 0 ≤ densK L0 A := by unfold densK; positivity
  rw [dens_eq, dens_eq]
  apply div_le_div_of_nonneg_left hK hEv
  unfold densE
  nlinarith [mul_nonneg (mul_nonneg (sub_pos.2 hLL).le hD) (sub_nonneg.2 hvw)]

/-! ### A quadratic is positive on `[0, T]` -/

/-- The four elementary reasons for a quadratic `α + b v + a v²` with `α > 0` and positive value at
`T` to stay above a positive constant on `[0, T]`. -/
theorem quad_lower {a b α T : ℝ} (hT : 0 ≤ T) (hα : 0 < α) (hQ : 0 < α + b * T + a * T ^ 2)
    (hc : a ≤ 0 ∨ 0 ≤ b ∨ b ^ 2 < 4 * a * α ∨ 2 * a * T ≤ -b) :
    ∃ m : ℝ, 0 < m ∧ ∀ v, 0 ≤ v → v ≤ T → m ≤ α + b * v + a * v ^ 2 := by
  by_cases ha : a ≤ 0
  · -- concave: above the chord through `(0, α)` and `(T, Q T)`
    refine ⟨min α (α + b * T + a * T ^ 2), lt_min hα hQ, fun v hv hvT => ?_⟩
    have hmα := min_le_left α (α + b * T + a * T ^ 2)
    have hmQ := min_le_right α (α + b * T + a * T ^ 2)
    generalize min α (α + b * T + a * T ^ 2) = m at hmα hmQ ⊢
    rcases hT.eq_or_lt with hT0 | hTpos
    · have hv0 : v = 0 := by linarith
      subst hv0
      simpa using hmα
    · have h1 : 0 ≤ (T - v) * (α - m) := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ v * (α + b * T + a * T ^ 2 - m) := mul_nonneg hv (by linarith)
      have h3 : 0 ≤ (-a) * v * (T * (T - v)) :=
        mul_nonneg (mul_nonneg (by linarith) hv) (mul_nonneg hT (by linarith))
      have h4 : T * m ≤ T * (α + b * v + a * v ^ 2) := by nlinarith [h1, h2, h3]
      exact le_of_mul_le_mul_left h4 hTpos
  · have ha : 0 < a := not_le.1 ha
    rcases hc with h | h | h | h
    · exact absurd h (not_le.2 ha)
    · -- nondecreasing
      exact ⟨α, hα, fun v hv _ => by nlinarith [mul_nonneg hv (add_nonneg h (mul_nonneg ha.le hv))]⟩
    · -- no real root
      refine ⟨(4 * a * α - b ^ 2) / (4 * a), div_pos (by linarith) (by linarith), fun v hv _ => ?_⟩
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg (2 * a * v + b)]
    · -- nonincreasing on `[0, T]`
      refine ⟨α + b * T + a * T ^ 2, hQ, fun v hv hvT => ?_⟩
      have h1 : 0 ≤ T - v := by linarith
      have h2 : 0 ≤ -(a * (v + T) + b) := by nlinarith [mul_nonneg ha.le h1]
      nlinarith [mul_nonneg h1 h2]

/-! ### The shape `α + β v - γ u(v)` -/

/-- The cleared form of the shape gate. -/
theorem shape_mul {A D α β γ v : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) :
    (α + β * v - γ * sel A D v) * (1 + D * v) =
      α + (α * D + β - γ * A) * v + (β * D) * v ^ 2 := by
  have hx : 1 + D * v ≠ 0 := (one_add_pos hD hv).ne'
  unfold sel
  field_simp
  ring

theorem shape_QT {A D α β γ T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T) :
    (α + β * T) * (1 + D * T) - γ * A * T = (α + β * T - γ * sel A D T) * (1 + D * T) := by
  rw [shape_mul hD hT]
  ring

/-- Generic lemma: `ShapePos` gives a uniform reserve for `α + β v - γ · sel A D v` on `[0, T]`. -/
theorem shape_unifPos {A D α β γ T : ℝ} (hD : 0 < D) (hT : 0 ≤ T) (h : ShapePos A D α β γ T) :
    UnifPos (fun v => α + β * v - γ * sel A D v) 0 T := by
  obtain ⟨hα, hQT, hc⟩ := h
  have hQ : 0 < α + (α * D + β - γ * A) * T + (β * D) * T ^ 2 := by
    have e : (α + β * T) * (1 + D * T) - γ * A * T =
        α + (α * D + β - γ * A) * T + (β * D) * T ^ 2 := by ring
    linarith
  have hc' : β * D ≤ 0 ∨ 0 ≤ α * D + β - γ * A ∨ (α * D + β - γ * A) ^ 2 < 4 * (β * D) * α ∨
      2 * (β * D) * T ≤ -(α * D + β - γ * A) := by
    rcases hc with h | h | h | h
    · exact Or.inl (mul_nonpos_of_nonpos_of_nonneg h hD.le)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨m, hm, hmQ⟩ := quad_lower hT hα hQ hc'
  have hxT : 0 < 1 + D * T := one_add_pos hD.le hT
  refine ⟨m / (1 + D * T), div_pos hm hxT, fun v hv hvT => ?_⟩
  have hx : 0 < 1 + D * v := one_add_pos hD.le hv
  have key : m ≤ (α + β * v - γ * sel A D v) * (1 + D * v) := by
    rw [shape_mul hD.le hv]
    exact hmQ v hv hvT
  have h1 : m / (1 + D * T) * (1 + D * v) ≤ (α + β * v - γ * sel A D v) * (1 + D * v) := by
    calc m / (1 + D * T) * (1 + D * v) ≤ m / (1 + D * T) * (1 + D * T) := by
          apply mul_le_mul_of_nonneg_left _ (div_pos hm hxT).le
          nlinarith [mul_le_mul_of_nonneg_left hvT hD.le]
      _ = m := div_mul_cancel₀ _ hxT.ne'
      _ ≤ _ := key
  exact le_of_mul_le_mul_right h1 hx

theorem unifPos_of_shape {f : ℝ → ℝ} {A D α β γ T : ℝ} (hD : 0 < D) (hT : 0 ≤ T)
    (hf : ∀ v, f v = α + β * v - γ * sel A D v) (h : ShapePos A D α β γ T) :
    UnifPos f 0 T := by
  have e : f = fun v => α + β * v - γ * sel A D v := funext hf
  rw [e]
  exact shape_unifPos hD hT h

/-- A concave (`β ≤ 0`) shape with `α > 0` is `ShapePos` as soon as its value at `T` is positive. -/
theorem shapePos_of_nonpos {A D α β γ T : ℝ} (hD : 0 < D) (hT : 0 ≤ T) (hβ : β ≤ 0)
    (hα : 0 < α) (hg : 0 < α + β * T - γ * sel A D T) : ShapePos A D α β γ T :=
  ⟨hα, by rw [shape_QT hD.le hT]; exact mul_pos hg (one_add_pos hD.le hT), Or.inl hβ⟩

/-- The shape `s + v - u(v)` of the retained width: `ShapePos` for `s > 0`, `A ≤ 1`. -/
theorem shapePos_width {A D s T : ℝ} (hD : 0 < D) (hT : 0 ≤ T) (hs : 0 < s) (hA1 : A ≤ 1) :
    ShapePos A D s 1 1 T := by
  refine ⟨hs, ?_, Or.inr (Or.inl ?_)⟩
  · nlinarith [mul_nonneg (mul_nonneg hs.le hD.le) hT, mul_nonneg hT (sub_nonneg.2 hA1),
      mul_nonneg hD.le (mul_nonneg hT hT)]
  · nlinarith [mul_nonneg hs.le hD.le]

/-! ### The five gates of the shape `α + β v - γ u(v)` -/

theorem gRetainedCap_eq (B0 L0 c0 B L A D v : ℝ) :
    gRetainedCap B0 L0 c0 B L A D v =
      (c0 - cross B0 L0 B L) + (-1) * v - (6 * c0 - 1) * sel A D v := by
  unfold gRetainedCap packed width
  ring

theorem gRetainedWidth_eq (B0 L0 B L A D v : ℝ) :
    gRetainedWidth B0 L0 B L A D v = cross B0 L0 B L + 1 * v - 1 * sel A D v := by
  unfold gRetainedWidth width
  ring

theorem gPrincipal_eq (B0 L0 B L A D v : ℝ) :
    gPrincipal B0 L0 B L A D v =
      (1 - B + (L - 2) * cross B0 L0 B L) + (L - 2) * v - 9 / 2 * sel A D v := by
  unfold gPrincipal width
  ring

theorem gSecondRef_eq (B0 L0 B L A D v : ℝ) :
    gSecondRef B0 L0 B L A D v =
      (1 / 20 + 3 / 2 * (1 - B) + (3 / 2 * L - 5 / 2) * cross B0 L0 B L)
        + (3 / 2 * L - 5 / 2) * v - 9 / 2 * sel A D v := by
  unfold gSecondRef width
  ring

theorem gSecondDiag_eq (B0 L0 B L A D v : ℝ) :
    gSecondDiag B0 L0 B L A D v =
      (1 - B + (L - 1) * cross B0 L0 B L) + (L - 1) * v - 4 * sel A D v := by
  unfold gSecondDiag width
  ring

/-! ### The monotone gates -/

theorem unifPos_qLower {B0 L0 L A D T : ℝ} (hLL : L < L0) (h6 : 0 < 6 * B0 - L0) (hL0 : 0 < L0)
    (hA : 0 < A) (hD : 0 ≤ D) (h : 1 / 2 < dens B0 L0 L A D T) :
    UnifPos (gQLower B0 L0 L A D) 0 T :=
  ⟨dens B0 L0 L A D T - 1 / 2, by linarith, fun v hv hvT => by
    have := dens_antitone (B0 := B0) hLL h6 hL0 hA hD hv hvT
    unfold gQLower
    linarith⟩

theorem unifPos_qFloor {qf B0 L0 L A D T : ℝ} (hLL : L < L0) (h6 : 0 < 6 * B0 - L0) (hL0 : 0 < L0)
    (hA : 0 < A) (hD : 0 ≤ D) (h : qf < dens B0 L0 L A D T) :
    UnifPos (gQFloor qf B0 L0 L A D) 0 T :=
  ⟨dens B0 L0 L A D T - qf, by linarith, fun v hv hvT => by
    have := dens_antitone (B0 := B0) hLL h6 hL0 hA hD hv hvT
    unfold gQFloor
    linarith⟩

theorem unifPos_qUpper {B0 L0 L A D T : ℝ} (hLL : L < L0) (h6 : 0 < 6 * B0 - L0) (hL0 : 0 < L0)
    (hA : 0 < A) (hD : 0 ≤ D) (h : dens B0 L0 L A D 0 < 3 / 4) :
    UnifPos (gQUpper B0 L0 L A D) 0 T :=
  ⟨3 / 4 - dens B0 L0 L A D 0, by linarith, fun v hv _ => by
    have := dens_antitone (B0 := B0) hLL h6 hL0 hA hD (le_refl (0 : ℝ)) hv
    unfold gQUpper
    linarith⟩

theorem unifPos_H {A D T : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (h : 6 * sel A D T < 1 / 10) :
    UnifPos (gHLower A D) 0 T :=
  ⟨1 / 10 - 6 * sel A D T, by linarith, fun v hv hvT => by
    have := sel_mono hA.le hD hv hvT
    unfold gHLower packed
    linarith⟩

theorem unifPos_refUpper {B0 L0 B L A D T : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (h : 0 < gRefUpper B0 L0 B L A D T) : UnifPos (gRefUpper B0 L0 B L A D) 0 T :=
  ⟨gRefUpper B0 L0 B L A D T, h, fun v hv hvT => by
    have := sel_mono hA.le hD hv hvT
    unfold gRefUpper width
    linarith⟩

theorem unifPos_lowPerWidth {L0 A D T : ℝ} (hL0 : 0 < L0) (hA : 0 < A) (hD : 0 ≤ D)
    (hT : 0 ≤ T) : UnifPos (gLowPerWidth L0 A D) 0 T := by
  have hxT := one_add_pos hD hT
  refine ⟨gLowPerWidth L0 A D T, by unfold gLowPerWidth; positivity, fun v hv hvT => ?_⟩
  have hx := one_add_pos hD hv
  unfold gLowPerWidth
  apply div_le_div_of_nonneg_left (by positivity) hx
  nlinarith [mul_le_mul_of_nonneg_left hvT hD]

theorem unifPos_selDeriv {A D T : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hT : 0 ≤ T) :
    UnifPos (gSelDeriv A D) 0 T := by
  have hxT := one_add_pos hD hT
  refine ⟨gSelDeriv A D T, by unfold gSelDeriv; positivity, fun v hv hvT => ?_⟩
  have hx := one_add_pos hD hv
  unfold gSelDeriv
  apply div_le_div_of_nonneg_left hA.le (pow_pos hx 2)
  exact pow_le_pow_left₀ hx.le (by nlinarith [mul_le_mul_of_nonneg_left hvT hD]) 2

end Gates1D

open Gates1D

/-- **The one-variable gates of a marked density step from scalar endpoint data.**

Let `s0 = cross B0 L0 B L`, `vmax = c - s0`, `u = sel A D`, `q = dens B0 L0 L A D`.
All hypotheses except `hhigh` are scalar inequalities between rational expressions in the
parameters (use `norm_num [dens, sel, cross, gRetainedCap, gRefUpper, ShapePos]`):

* standing: `0 < A`, `0 < D`, `L < L0`, `0 < L0`, `0 < 6 B0 - L0`, `0 < vmax`;
* `hqlow : 1/2 < q(vmax)`, `hqfloor : qf < q(vmax)`, `hqup : q(0) < 3/4`;
* `hH : 6 u(vmax) < 1/10` (packed radius `H ≥ 9/10`);
* `hc0 : s0 < c0` and `hcap : 0 < gRetainedCap(vmax)` (retained cap; the value at `0` is `c0 - s0`);
* `hs0 : 0 < s0` and `hA1 : A ≤ 1` (retained width `s0 + v - u(v) ≥ s0`);
* `hrefup : 0 < gRefUpper(vmax)` (`1/3 - 2 w - 3 u`);
* `hprin`, `hsref`, `hsdia`: `ShapePos` for the principal, second reference and second diagonal
  gates `α + β v - γ u(v)` with `(α, β, γ)` read off from `width = s0 + v`;
* `hhigh`: the field `high_marked`, unchanged.

The reserves of the lower-bounded gates are the endpoint values, so the structure is obtained
without any case analysis on the parameters beyond `ShapePos`. -/
theorem hybridGatesM_of_scalar {qf B0 L0 c0 B L c A D : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hLL : L < L0) (hL0 : 0 < L0) (h6 : 0 < 6 * B0 - L0)
    (hw : 0 < c - cross B0 L0 B L)
    (hqlow : 1 / 2 < dens B0 L0 L A D (c - cross B0 L0 B L))
    (hqfloor : qf < dens B0 L0 L A D (c - cross B0 L0 B L))
    (hqup : dens B0 L0 L A D 0 < 3 / 4)
    (hH : 6 * sel A D (c - cross B0 L0 B L) < 1 / 10)
    (hc0 : cross B0 L0 B L < c0)
    (hcap : 0 < gRetainedCap B0 L0 c0 B L A D (c - cross B0 L0 B L))
    (hs0 : 0 < cross B0 L0 B L) (hA1 : A ≤ 1)
    (hrefup : 0 < gRefUpper B0 L0 B L A D (c - cross B0 L0 B L))
    (hprin : ShapePos A D (1 - B + (L - 2) * cross B0 L0 B L) (L - 2) (9 / 2)
      (c - cross B0 L0 B L))
    (hsref : ShapePos A D (1 / 20 + 3 / 2 * (1 - B) + (3 / 2 * L - 5 / 2) * cross B0 L0 B L)
      (3 / 2 * L - 5 / 2) (9 / 2) (c - cross B0 L0 B L))
    (hsdia : ShapePos A D (1 - B + (L - 1) * cross B0 L0 B L) (L - 1) 4 (c - cross B0 L0 B L))
    (hhigh : ∃ r : ℝ, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → ∀ ν,
      dens B0 L0 L A D v ≤ ν → ν ≤ 3 / 4 →
        r ≤ highJ B L (width B0 L0 B L v) (sel A D v) ν +
          QRH.RepeatedMarks.Source.gainC ν B0 L0 c0 (width B0 L0 B L v - sel A D v)
            (packed A D v)) :
    HybridGatesM qf B0 L0 c0 B L c A D where
  width_pos := hw
  sel_den_pos := fun v h0 _ => one_add_pos hD.le h0
  dens_den_pos := fun v h0 _ => densE_pos hLL h6 hA hD.le h0
  q_lower := unifPos_qLower hLL h6 hL0 hA hD.le hqlow
  q_upper := unifPos_qUpper hLL h6 hL0 hA hD.le hqup
  q_floor := unifPos_qFloor hLL h6 hL0 hA hD.le hqfloor
  H_lower := unifPos_H hA hD.le hH
  retained_cap :=
    unifPos_of_shape hD hw.le (gRetainedCap_eq B0 L0 c0 B L A D)
      (shapePos_of_nonpos hD hw.le (by norm_num) (sub_pos.2 hc0)
        (by rw [← gRetainedCap_eq]; exact hcap))
  retained_width :=
    unifPos_of_shape hD hw.le (gRetainedWidth_eq B0 L0 B L A D) (shapePos_width hD hw.le hs0 hA1)
  low_identity := fun v h0 _ =>
    lowDefect_eq B0 L0 L A D v (one_add_pos hD.le h0).ne' (densE_pos hLL h6 hA hD.le h0).ne'
  low_div_eq := fun v h0 _ =>
    lowDefect_div_eq B0 L0 L A D v h0.ne' (one_add_pos hD.le h0.le).ne'
      (densE_pos hLL h6 hA hD.le h0.le).ne'
  low_per_excess_width := unifPos_lowPerWidth hL0 hA hD.le hw.le
  high_marked := hhigh
  principal_reference :=
    unifPos_of_shape hD hw.le (gPrincipal_eq B0 L0 B L A D) hprin
  second_reference :=
    unifPos_of_shape hD hw.le (gSecondRef_eq B0 L0 B L A D) hsref
  second_diagonal :=
    unifPos_of_shape hD hw.le (gSecondDiag_eq B0 L0 B L A D) hsdia
  reference_upper_positive := unifPos_refUpper hA hD.le hrefup
  sel_hasDerivAt := fun v h0 _ => sel_hasDerivAt A D v (one_add_pos hD.le h0).ne'
  selection_monotonicity := unifPos_selDeriv hA hD.le hw.le

#print axioms hybridGatesM_of_scalar

end QRH.ArviUniformChain
