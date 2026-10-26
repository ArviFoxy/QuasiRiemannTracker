/- Mixed source step, ledger N4: the virtual nodes.

A piece of the residual whose selected block has width `δ` is paid at the *virtual node*
`vnode n low b δ`, a genuine Collet `Source` evaluated at the width `b - δ`:
  `vnode n low b δ = ⟨n.B - n.L·δ, n.L, n.cap, n.q, n.allowance, vfee n low b δ, n.highFee⟩`.
Its fee `vfee` is chosen so that Collet's formulas give, at the width `b - δ`,
  `sourceT = t` (the plain budget is unchanged), `sourceA = r + δ` (pool plus transfer) and
  `sourceF = 1 - 6r - 6δ` (`vnode_T`, `vnode_A`, `vnode_F`).
At the top node `δ = d = sourceD n low b` the fee is the actual fee `r` (`vfee_top`).

The width `b` is rational: the width grid of the step can be taken rational at no cost (any rational
width delta below the real one works, `Ledger/Geometry.lean`), so the nodes are rational `Source`s and
no real-field twin is needed. `vnode_A` needs Collet's denominator `sourceDen n low = 1 - 6qβ` to be
nonzero; this is the one gate that `SourceValid3` does not imply (all its gates are polynomial in `qβ`).

From `SourceValid3` this file derives, at every rational node `δ ∈ [0, d]`, the fields of Collet's
`RealGeometry` that hold at the node (`RealGeometryLow`): the node quantities are affine in `δ` and the
gates of `SourceValid3` are exactly their values at `δ = d`, with the slope of the right sign. -/
import Submissions.arvi_mixed_step.Finite.HighGate3
import Submissions.hailey_collet_1252270103.Record1252270103StepScalar.Geometry
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.MixedStep.Ledger
open Record1252270103Finite QRH.MixedStep.Finite QRH.Record1252270103Graph

/-! ## The virtual node -/

/-- The fee of the virtual node at transferred width `δ`: `r(1 - 6qβ) + δ·den3 - q·X₀`. -/
def vfee (n low : Source) (b δ : ℚ) : ℚ :=
  n.lowFee*(1 - 6*n.q*(low.B/low.L)) + δ*sourceDen3 n low - n.q*sourceX0 n low b

/-- The fee of the two-parameter node: amplifier shift `δ`, budget/width shift `θ`. -/
def vfee2 (n low : Source) (b δ θ : ℚ) : ℚ := vfee n low b δ - n.q*(δ - θ)

/-- The two-parameter virtual node: plain budget and width shifted by `θ` (evaluated at the width
`b - θ`), amplifier shifted by `δ`. The residual of a transfer of actual width `δ_act ∈ [θ, δ]` sits
inside its face: `m₁ + m₂ + L·Σ_res ≤ B - L·θ` and `Σ_res ≤ b - θ`. -/
def vnode2 (n low : Source) (b δ θ : ℚ) : Source :=
  ⟨n.B - n.L*θ, n.L, n.cap, n.q, n.allowance, vfee2 n low b δ θ, n.highFee⟩

/-- The one-parameter virtual node (`θ = δ`), evaluated at the width `b - δ`. -/
def vnode (n low : Source) (b δ : ℚ) : Source := vnode2 n low b δ δ

@[simp] lemma vnode2_B (n low : Source) (b δ θ : ℚ) : (vnode2 n low b δ θ).B = n.B - n.L*θ := rfl
@[simp] lemma vnode2_L (n low : Source) (b δ θ : ℚ) : (vnode2 n low b δ θ).L = n.L := rfl
@[simp] lemma vnode2_cap (n low : Source) (b δ θ : ℚ) : (vnode2 n low b δ θ).cap = n.cap := rfl
@[simp] lemma vnode2_q (n low : Source) (b δ θ : ℚ) : (vnode2 n low b δ θ).q = n.q := rfl
@[simp] lemma vnode2_allowance (n low : Source) (b δ θ : ℚ) :
    (vnode2 n low b δ θ).allowance = n.allowance := rfl
@[simp] lemma vnode2_lowFee (n low : Source) (b δ θ : ℚ) :
    (vnode2 n low b δ θ).lowFee = vfee2 n low b δ θ := rfl
@[simp] lemma vnode2_highFee (n low : Source) (b δ θ : ℚ) :
    (vnode2 n low b δ θ).highFee = n.highFee := rfl

@[simp] lemma vnode_B (n low : Source) (b δ : ℚ) : (vnode n low b δ).B = n.B - n.L*δ := rfl
@[simp] lemma vnode_L (n low : Source) (b δ : ℚ) : (vnode n low b δ).L = n.L := rfl
@[simp] lemma vnode_cap (n low : Source) (b δ : ℚ) : (vnode n low b δ).cap = n.cap := rfl
@[simp] lemma vnode_q (n low : Source) (b δ : ℚ) : (vnode n low b δ).q = n.q := rfl
@[simp] lemma vnode_allowance (n low : Source) (b δ : ℚ) :
    (vnode n low b δ).allowance = n.allowance := rfl
@[simp] lemma vnode_lowFee (n low : Source) (b δ : ℚ) :
    (vnode n low b δ).lowFee = vfee n low b δ := by
  simp [vnode, vfee2]
@[simp] lemma vnode_highFee (n low : Source) (b δ : ℚ) :
    (vnode n low b δ).highFee = n.highFee := rfl

theorem vnode2_den (n low : Source) (b δ θ : ℚ) :
    sourceDen (vnode2 n low b δ θ) low = sourceDen n low := rfl

/-- The plain budget is unchanged: the budget and the width move together. -/
theorem vnode2_T (n low : Source) (b δ θ : ℚ) :
    sourceT (vnode2 n low b δ θ) (b - θ) = sourceT n b := by
  simp only [sourceT, vnode2]; ring

/-- Collet's amplifier at the node is the pool plus the transfer `δ`. -/
theorem vnode2_A (n low : Source) (b δ θ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceA (vnode2 n low b δ θ) low (b - θ) = n.lowFee + δ := by
  have hT := vnode2_T n low b δ θ
  simp only [sourceA, vnode2_den] at hT ⊢
  rw [div_eq_iff hden, hT]
  simp only [vnode2, vfee2, vfee, sourceDen3, sourceX0, sourceDen]
  ring

theorem vnode2_F (n low : Source) (b δ θ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceF (vnode2 n low b δ θ) low (b - θ) = 1 - 6*n.lowFee - 6*δ := by
  rw [sourceF, vnode2_A n low b δ θ hden]; ring

theorem vnode_T (n low : Source) (b δ : ℚ) : sourceT (vnode n low b δ) (b - δ) = sourceT n b :=
  vnode2_T n low b δ δ

theorem vnode_A (n low : Source) (b δ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceA (vnode n low b δ) low (b - δ) = n.lowFee + δ :=
  vnode2_A n low b δ δ hden

theorem vnode_F (n low : Source) (b δ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceF (vnode n low b δ) low (b - δ) = 1 - 6*n.lowFee - 6*δ :=
  vnode2_F n low b δ δ hden

/-- At the top node `δ = d` the one-parameter fee is the actual fee. -/
theorem vfee_top (n low : Source) (b : ℚ) (hden3 : sourceDen3 n low ≠ 0) :
    vfee n low b (sourceD n low b) = n.lowFee := by
  simp only [vfee, sourceD]
  rw [div_mul_cancel₀ _ hden3]
  ring

/-- The one-parameter fee falls short of the actual fee by `(d - δ)·den3`. -/
theorem vfee_sub (n low : Source) (b δ : ℚ) (hden3 : sourceDen3 n low ≠ 0) :
    vfee n low b δ - n.lowFee = (δ - sourceD n low b)*sourceDen3 n low := by
  have h := vfee_top n low b hden3
  have e : vfee n low b δ - vfee n low b (sourceD n low b) =
      (δ - sourceD n low b)*sourceDen3 n low := by simp only [vfee]; ring
  rw [h] at e; exact e

/-- At the top node the two-parameter fee is the actual fee minus `q(d - θ)`. -/
theorem vfee2_top (n low : Source) (b θ : ℚ) (hden3 : sourceDen3 n low ≠ 0) :
    vfee2 n low b (sourceD n low b) θ = n.lowFee - n.q*(sourceD n low b - θ) := by
  rw [vfee2, vfee_top n low b hden3]

noncomputable section

/-! ## Real forms at the node width -/

theorem vnode2R_T (n low : Source) (b δ θ : ℚ) :
    sourceTReal (vnode2 n low b δ θ) ((b - θ : ℚ) : ℝ) = sourceTReal n (b:ℝ) := by
  rw [sourceTReal_rat, sourceTReal_rat, vnode2_T]

theorem vnode2R_A (n low : Source) (b δ θ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceAReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) = (n.lowFee:ℝ) + (δ:ℝ) := by
  rw [sourceAReal_rat, vnode2_A n low b δ θ hden]; push_cast; ring

theorem vnode2R_F (n low : Source) (b δ θ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceFReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) = 1 - 6*(n.lowFee:ℝ) - 6*(δ:ℝ) := by
  rw [sourceFReal_rat, vnode2_F n low b δ θ hden]; push_cast; ring

theorem vnodeR_T (n low : Source) (b δ : ℚ) :
    sourceTReal (vnode n low b δ) ((b - δ : ℚ) : ℝ) = sourceTReal n (b:ℝ) := vnode2R_T n low b δ δ

theorem vnodeR_A (n low : Source) (b δ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceAReal (vnode n low b δ) low ((b - δ : ℚ) : ℝ) = (n.lowFee:ℝ) + (δ:ℝ) :=
  vnode2R_A n low b δ δ hden

theorem vnodeR_F (n low : Source) (b δ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceFReal (vnode n low b δ) low ((b - δ : ℚ) : ℝ) = 1 - 6*(n.lowFee:ℝ) - 6*(δ:ℝ) :=
  vnode2R_F n low b δ δ hden

theorem sourceDReal_eq (n low : Source) (b : ℚ) : sourceDReal n low (b:ℝ) = (sourceD n low b:ℝ) :=
  sourceDReal_rat n low b

/-! ## The scalar gates of `SourceValid3` over the reals -/

/-- `scalarGate3` at a real width. -/
def scalarGate3Real (n low : Source) (b : ℝ) (j : Fin 18) : ℝ :=
  let a : ℝ := n.lowFee
  let d := sourceDReal n low b
  let A := a + d
  let t := sourceTReal n b
  let T := t + b
  let F := sourceF3Real n low b
  let e : ℝ := n.allowance
  let fee : ℝ := n.highFee
  let Lref := 49/100 - (9/2)*b
  ![(sourceDen3 n low:ℝ), b - 2*e, a, 1/75 - A, F - T/2 - 4*e,
    (low.B:ℝ)*F - t - b - 4*e, 1 - (n.q:ℝ)*(low.cap:ℝ),
    (n.lowFee:ℝ) - ((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ) + (n.q:ℝ)*(low.cap:ℝ) + 4)*e - 10*e,
    a - 20*e, Lref, 1 - Lref - 1/2 - (9/2)*b - 10*e,
    5/6 + (499/1000)*Lref - T - 9*A - fee,
    1 - T - 5*A - fee, 1 - 1/50 - T - 4*A - fee,
    1 - 1/50 - T - (9/2)*A - fee, Lref - 7*A - fee,
    b - 2*e - d, d + 1/10^30] j

theorem scalarGate3Real_rat (n low : Source) (b : ℚ) (j : Fin 18) :
    scalarGate3Real n low (b:ℝ) j = (scalarGate3 n low b j : ℝ) := by
  have hd := sourceDReal_rat n low b
  have hF := sourceF3Real_rat n low b
  have hT := sourceTReal_rat n b
  fin_cases j <;> simp [scalarGate3Real, scalarGate3, hd, hF, hT]

theorem sourceDReal_affine (n low : Source) : WidthAffine (sourceDReal n low) := by
  intro x y t; simp only [sourceDReal, sourceTReal]; ring

theorem sourceF3Real_affine (n low : Source) : WidthAffine (sourceF3Real n low) := by
  intro x y t; simp only [sourceF3Real, sourceDReal, sourceTReal]; ring

theorem scalarGate3Real_affine (n low : Source) (j : Fin 18) :
    WidthAffine (fun b => scalarGate3Real n low b j) := by
  intro x y t
  fin_cases j <;> simp [scalarGate3Real, sourceF3Real, sourceDReal, sourceTReal] <;> ring

def weakCap3Real (n low : Source) (b : ℝ) : ℝ :=
  (low.cap:ℝ)*sourceF3Real n low b - ((low.B:ℝ)*sourceF3Real n low b - sourceTReal n b)/(low.L:ℝ)

theorem weakCap3Real_rat (n low : Source) (b : ℚ) :
    weakCap3Real n low (b:ℝ) = (weakCap3 n low b : ℝ) := by
  simp [weakCap3Real, weakCap3, sourceF3Real_rat, sourceTReal_rat]

theorem weakCap3Real_affine (n low : Source) : WidthAffine (weakCap3Real n low) := by
  intro x y t; simp only [weakCap3Real, sourceF3Real, sourceDReal, sourceTReal]; ring

/-- The scalar gates and the weak cap on the whole width cell. -/
theorem scalar3_full_width (n low h : Source) (hv : SourceValidC3 n low h) {b : ℝ}
    (hb : b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    (∀ j, 0 < scalarGate3Real n low b j) ∧ 0 ≤ weakCap3Real n low b := by
  have hleft := hv.2.2.2.2.2.2.2.2.2.2.2.2 (crossing n low) (by simp)
  have hright := hv.2.2.2.2.2.2.2.2.2.2.2.2 n.cap (by simp)
  refine ⟨fun j => ?_, ?_⟩
  · apply width_affine_positive (scalarGate3Real_affine n low j) hb
    · rw [scalarGate3Real_rat]; exact_mod_cast hleft.1 j
    · rw [scalarGate3Real_rat]; exact_mod_cast hright.1 j
  · apply width_affine_nonnegative (weakCap3Real_affine n low) hb
    · rw [weakCap3Real_rat]; exact_mod_cast hleft.2.1
    · rw [weakCap3Real_rat]; exact_mod_cast hright.2.1

/-! ## Basic facts at the actual width -/

/-- The fields of `SourceValidC3` that every later lemma uses, in real form. -/
structure Shape3 (n low : Source) : Prop where
  B_pos : 0 < (n.B:ℝ)
  B_le : (n.B:ℝ) ≤ 1
  L_gt : 1 < (n.L:ℝ)
  q_half : (1/2:ℝ) ≤ n.q
  q_lt : (n.q:ℝ) < 3/4
  L_lt : (n.L:ℝ) < low.L
  cross_nonneg : 0 ≤ (crossing n low:ℝ)
  cross_cap : (crossing n low:ℝ) ≤ n.cap

theorem shape3_of (n low h : Source) (hv : SourceValidC3 n low h) : Shape3 n low := by
  obtain ⟨hB, hB1, hL, _, _, hq, hq1, hLL, hc0, hc1, _⟩ := hv
  refine ⟨by exact_mod_cast hB, by exact_mod_cast hB1, by exact_mod_cast hL, ?_, ?_,
    by exact_mod_cast hLL, by exact_mod_cast hc0, by exact_mod_cast hc1⟩
  · have hh := (Rat.cast_le (K:=ℝ)).mpr hq; norm_num at hh; exact hh
  · have hh := (Rat.cast_lt (K:=ℝ)).mpr hq1; norm_num at hh; exact hh

/-- The selected width is nonnegative on the cell (the live width `X₀` is at least `L e/Λ₀ ≥ 0`
past the crossing). -/
theorem sourceDReal_nonneg (n low h : Source) (hv : SourceValidC3 n low h) (hlow : ParentGood low)
    (he : 0 ≤ (n.allowance:ℝ)) {b : ℝ} (hb : b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    0 ≤ sourceDReal n low b := by
  have S := shape3_of n low h hv
  have hg := (scalar3_full_width n low h hv hb).1
  have g0 := hg 0
  have g2 := hg 2
  simp only [scalarGate3Real] at g0 g2
  norm_num at g0 g2
  have hL0 : 0 < (low.L:ℝ) := by
    have := hlow.2.2.1; have h1 : (1:ℝ) < low.L := by exact_mod_cast this
    linarith
  have hB0 : 0 ≤ (low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hq0 : 0 ≤ (n.q:ℝ) := by linarith [S.q_half]
  have hdiff : 0 < (low.L:ℝ) - n.L := by linarith [S.L_lt]
  have hcross : (crossing n low:ℝ) = ((low.B:ℝ) - n.B)/((low.L:ℝ) - n.L) := by
    simp [crossing]
  have hx : (low.B:ℝ) - n.B ≤ ((low.L:ℝ) - n.L)*b := by
    have := hb.1; rw [hcross, div_le_iff₀ hdiff] at this; linarith
  have hX : 0 ≤ b + (sourceTReal n b - low.B)/low.L := by
    have hnum : 0 ≤ (low.L:ℝ)*b + (sourceTReal n b - low.B) := by
      simp only [sourceTReal]
      have hLe : 0 ≤ (n.L:ℝ)*(n.allowance:ℝ) := mul_nonneg (by linarith [S.L_gt]) he
      nlinarith
    have : b + (sourceTReal n b - low.B)/low.L = ((low.L:ℝ)*b + (sourceTReal n b - low.B))/low.L := by
      field_simp
    rw [this]; exact div_nonneg hnum hL0.le
  have g0' : (0:ℝ) < sourceDen3 n low := by exact_mod_cast g0
  have g2' : (0:ℝ) < n.lowFee := by exact_mod_cast g2
  simp only [sourceDReal]
  apply div_nonneg _ g0'.le
  have h6 : 0 ≤ 6*(n.q:ℝ)*((low.B:ℝ)/(low.L:ℝ))*(n.lowFee:ℝ) :=
    mul_nonneg (mul_nonneg (by linarith) (div_nonneg hB0 hL0.le)) g2'.le
  nlinarith [mul_nonneg hq0 hX]

theorem sourceD_nonneg (n low h : Source) (hv : SourceValidC3 n low h) (hlow : ParentGood low)
    (he : 0 ≤ (n.allowance:ℝ)) {b : ℚ} (hb : (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    0 ≤ sourceD n low b := by
  have := sourceDReal_nonneg n low h hv hlow he hb
  rw [sourceDReal_rat] at this; exact_mod_cast this

/-! ## The low geometry at a node -/

/-- Collet's `RealGeometry` (StepScalar/Geometry.lean) without the fields that fail or do not belong
at a virtual node: `denominator_pos` (the node denominator `1 - 6qβ` is negative on our chain; only
`denominator_ne` is kept), `low_fee_room` (the node fee is below `r` for `δ < d`), `weak_cap` (false at
`δ = 0`, see LEAN_NOTES), and the first-layer fields `reference_pos`, `reference_gap`, `centered_499`,
`first_tail`, `second_tail`, `mixed_tail`, `reference_tail` (they concern the actual width `b`, see
`MixedGeometry`). -/
structure RealGeometryLow (n low : Source) (b : ℝ) : Prop where
  lowL_pos : 0<(low.L:ℝ)
  denominator_ne : (sourceDen n low:ℝ) ≠ 0
  width_room : 2*(n.allowance:ℝ)<b
  a_pos : 0<sourceAReal n low b
  a_small : sourceAReal n low b<1/75
  raw_factor_room : (sourceTReal n b+b)/2+4*(n.allowance:ℝ)<sourceFReal n low b
  parent_budget_room : sourceTReal n b+b+4*(n.allowance:ℝ)<(low.B:ℝ)*sourceFReal n low b
  qcap_room : (n.q:ℝ)*(low.cap:ℝ)<1
  a_allowance : 20*(n.allowance:ℝ)<sourceAReal n low b
  fee_identity : sourceAReal n low b-(n.q:ℝ)*(b+(sourceTReal n b-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ))=(n.lowFee:ℝ)

/-- The node quantities in terms of the actual width: `t`, `r + δ`, `F' + 6(d - δ)`. -/
theorem vnode2_real (n low : Source) (b δ θ : ℚ) (hden : sourceDen n low ≠ 0) :
    sourceTReal (vnode2 n low b δ θ) ((b - θ : ℚ) : ℝ) = sourceTReal n (b:ℝ) ∧
    sourceAReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) = (n.lowFee:ℝ) + δ ∧
    sourceFReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) =
      sourceF3Real n low (b:ℝ) + 6*(sourceDReal n low (b:ℝ) - δ) := by
  refine ⟨vnode2R_T n low b δ θ, vnode2R_A n low b δ θ hden, ?_⟩
  rw [vnode2R_F n low b δ θ hden]; simp only [sourceF3Real]; ring

/-- **The low geometry at every two-parameter node** `0 ≤ θ ≤ δ ≤ d`. -/
theorem realGeometryLow_vnode2 (n low h : Source) (hv : SourceValidC3 n low h)
    (hlow : ParentGood low) (hden : sourceDen n low ≠ 0) (he : 0 ≤ (n.allowance:ℝ))
    {b δ θ : ℚ} (hb : (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ δ) (hδ : δ ≤ sourceD n low b) :
    RealGeometryLow (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) := by
  obtain ⟨hT, hA, hF⟩ := vnode2_real n low b δ θ hden
  have hL0 : 0 < (low.L:ℝ) := by
    have h1 : (1:ℝ) < low.L := by exact_mod_cast hlow.2.2.1
    linarith
  have hB0 : 0 ≤ (low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hg := (scalar3_full_width n low h hv hb).1
  have g1 := hg 1; have g2 := hg 2; have g3 := hg 3; have g4 := hg 4; have g5 := hg 5
  have g6 := hg 6; have g8 := hg 8; have g16 := hg 16
  simp only [scalarGate3Real] at g1 g2 g3 g4 g5 g6 g8 g16
  norm_num at g1 g2 g3 g4 g5 g6 g8 g16
  have hθ0' : (0:ℝ) ≤ θ := by exact_mod_cast hθ0
  have hθ' : (θ:ℝ) ≤ δ := by exact_mod_cast hθ
  have hδ0' : (0:ℝ) ≤ δ := le_trans hθ0' hθ'
  have hδ' : (δ:ℝ) ≤ sourceDReal n low (b:ℝ) := by rw [sourceDReal_rat]; exact_mod_cast hδ
  have hbθ : ((b - θ : ℚ) : ℝ) = (b:ℝ) - θ := by push_cast; ring
  have hFd : sourceF3Real n low (b:ℝ) = 1 - 6*(n.lowFee:ℝ) - 6*sourceDReal n low (b:ℝ) := rfl
  refine ⟨hL0, by exact_mod_cast hden, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbθ]; simp only [vnode2_allowance]; linarith
  · rw [hA]; linarith
  · rw [hA]; linarith
  · rw [hT, hF, hbθ]; simp only [vnode2_allowance]; linarith
  · rw [hT, hF, hbθ]; simp only [vnode2_allowance]
    have hm : 0 ≤ (low.B:ℝ)*(sourceDReal n low (b:ℝ) - δ) := mul_nonneg hB0 (by linarith)
    nlinarith
  · simp only [vnode2_q]; linarith
  · rw [hA]; simp only [vnode2_allowance]; linarith
  · exact QRH.Record1252270103StepScalar.fee_identity (vnode2 n low b δ θ) low _ hL0.ne'
      (by exact_mod_cast hden)

theorem realGeometryLow_vnode (n low h : Source) (hv : SourceValidC3 n low h)
    (hlow : ParentGood low) (hden : sourceDen n low ≠ 0) (he : 0 ≤ (n.allowance:ℝ))
    {b δ : ℚ} (hb : (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ sourceD n low b) :
    RealGeometryLow (vnode n low b δ) low ((b - δ : ℚ) : ℝ) :=
  realGeometryLow_vnode2 n low h hv hlow hden he hb hδ0 le_rfl hδ

/-- The amplifier at every node is at least the pool `r`, so `mesh < r/2` gives `mesh < a_v/2`. -/
theorem vnode2_amp_ge (n low : Source) (b δ θ : ℚ) (hden : sourceDen n low ≠ 0) (hδ0 : 0 ≤ δ) :
    (n.lowFee:ℝ) ≤ sourceAReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) := by
  rw [vnode2R_A n low b δ θ hden]
  have : (0:ℝ) ≤ δ := by exact_mod_cast hδ0
  linarith

end
end QRH.MixedStep.Ledger
#print axioms QRH.MixedStep.Ledger.vnode_A
#print axioms QRH.MixedStep.Ledger.vfee_top
#print axioms QRH.MixedStep.Ledger.realGeometryLow_vnode2
