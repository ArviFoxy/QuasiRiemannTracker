/- Mixed source step, ledger N7 (gate part): everything the fork consumes, from the certificates.

`MixedGeometry Kgraph n low h b reserve` bundles, at a rational width `b` of the cell:
* the shape of the step and the one extra gate `SourceValid3X` (Collet's denominator `1 - 6qβ` is
  negative, so the virtual amplifier formula is exact);
* the first-layer facts at the actual width `b`, with the mixed amplifier `A = r + d`, the scale
  `F' = 1 - 6r - 6d` and `T = t + b`. The MAIN twins of the design are exactly scalar gates 11 and 12
  of `SourceValid3`: `T + 9A + fee < 5/6 + 0.499·Lref` and `T + 5A + fee < 1`;
* for every rational `0 ≤ θ ≤ δ ≤ d` (node `vnode2 n low b δ θ`, width `b - θ`): the node identities,
  `RealGeometryLow`, the frozen price, the top price (`δ = d`, `q(d - θ) ≤ 6e`) and the actual HIGH
  gaps with one `reserve`, chosen before the width.

`mixed_geometry_of_valid3` proves it from `SourceValid3`, `SourceValid3X`, `ParentGood low` and a
positive allowance (`NFAccounting`). No further gate is needed:
* the §1d pool-only gate follows from scalar gate 5 (`pool_only_gate`, FrozenPrice.lean);
* the mesh constraint `mesh < r/2` implies `mesh < a_v/2` at every node (`vnode2_amp_ge`);
* the grid is free: nodes `{k·g < d} ∪ {d}`, budget shift `θ ∈ [δ - κ, δ]`, and the frozen slack
  `ε ≥ δw + g + κ`, all `≤ 6e`; the rational width grid costs nothing (`exists_rat_width_delta`,
  `activeWidthGrid_rat`). -/
import Submissions.arvi_mixed_step.Ledger.FrozenPrice
import Submissions.arvi_mixed_step.Ledger.Gaps
import Submissions.arvi_mixed_step.Finite.SourceValid3X
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.FixedWidthPhysicalCells
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.MixedStep.Ledger
noncomputable section
open Record1252270103Finite QRH.MixedStep.Finite QRH.Record1252270103Graph
open QRH.Record1252270103Source.PhysicalScalar QRH.Record1252270103Source.FixedWidthPhysical

/-! ## The rational width grid -/

/-- Any positive width delta can be replaced by a smaller positive rational one. -/
theorem exists_rat_width_delta (δ : ℝ) (hδ : 0 < δ) : ∃ δq : ℚ, 0 < δq ∧ (δq:ℝ) ≤ δ := by
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn hδ
  exact ⟨q, by exact_mod_cast hq0, hq1.le⟩

/-- With rational endpoints and a rational delta, every grid width is rational. -/
theorem activeWidthGrid_rat (cross cap δq : ℚ) {b : ℝ}
    (hb : b ∈ activeWidthGrid (cross:ℝ) (cap:ℝ) (δq:ℝ)) :
    ∃ bq : ℚ, (bq:ℝ) = b ∧ (bq:ℝ) ∈ Set.Icc (cross:ℝ) (cap:ℝ) := by
  have hI := activeWidthGrid_bounds _ _ _ b hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hb).1
  refine ⟨min cap (cross + (i:ℚ)*δq), ?_, ?_⟩
  · push_cast; rfl
  · have e : ((min cap (cross + (i:ℚ)*δq) : ℚ) : ℝ) = min (cap:ℝ) ((cross:ℝ) + (i:ℝ)*(δq:ℝ)) := by
      push_cast; rfl
    rw [e]; exact hI

/-! ## The bundle -/

/-- Everything the fork consumes at a rational width `b`. -/
structure MixedGeometry (Kgraph : ℚ) (n low h : Source) (b : ℚ) (reserve : ℝ) : Prop where
  -- shape
  parent : ParentGood n
  low_parent : ParentGood low
  high_parent : QRH.RepeatedMarks.Source.GainParametersK h
  q_half : (1/2:ℝ) ≤ n.q
  q_lt : (n.q:ℝ) < 3/4
  allowance_pos : 0 < (n.allowance:ℝ)
  den_ne : sourceDen n low ≠ 0
  den_neg : sourceDen n low < 0
  den3_pos : 0 < sourceDen3 n low
  width_mem : (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)
  reserve_pos : 0 < reserve
  -- first layer at the actual width `b`: A = r + d, F' = 1 - 6r - 6d, T = t + b
  d_rat : sourceDReal n low (b:ℝ) = (sourceD n low b:ℝ)
  d_nonneg : 0 ≤ sourceD n low b
  fee_pos : 0 < (n.lowFee:ℝ)
  live_room : 2*(n.allowance:ℝ) + sourceDReal n low (b:ℝ) < b
  amp_small : sourceAmp3Real n low (b:ℝ) < 1/75
  raw_factor_room : (sourceTReal n (b:ℝ)+b)/2+4*(n.allowance:ℝ) < sourceF3Real n low (b:ℝ)
  parent_budget_room : sourceTReal n (b:ℝ)+b+4*(n.allowance:ℝ) < (low.B:ℝ)*sourceF3Real n low (b:ℝ)
  qcap_room : (n.q:ℝ)*(low.cap:ℝ) < 1
  low_fee_room : ((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ)+(n.q:ℝ)*(low.cap:ℝ)+4)*(n.allowance:ℝ)+
    10*(n.allowance:ℝ) < (n.lowFee:ℝ)
  fee_allowance : 20*(n.allowance:ℝ) < (n.lowFee:ℝ)
  reference_pos : 0 < 49/100-(Kgraph:ℝ)*b
  reference_gap : 1/2+(Kgraph:ℝ)*b+10*(n.allowance:ℝ) < 1-(49/100-(Kgraph:ℝ)*b)
  /-- MAIN twin, centered complement (design: `T + 9(a+d) + fee < 5/6 + 0.499·Lref`; scalar gate 11). -/
  centered_twin : sourceTReal n (b:ℝ)+b+9*sourceAmp3Real n low (b:ℝ)+(n.highFee:ℝ) <
    5/6+(499/1000)*(49/100-(Kgraph:ℝ)*b)
  /-- MAIN twin, zero frequency (design: `T + 5(a+d) + fee < 1`; scalar gate 12). -/
  zero_twin : sourceTReal n (b:ℝ)+b+5*sourceAmp3Real n low (b:ℝ)+(n.highFee:ℝ) < 1
  second_tail : sourceTReal n (b:ℝ)+b+4*sourceAmp3Real n low (b:ℝ)+(n.highFee:ℝ) < 1-1/50
  mixed_tail : sourceTReal n (b:ℝ)+b+(9/2)*sourceAmp3Real n low (b:ℝ)+(n.highFee:ℝ) < 1-1/50
  reference_tail : 7*sourceAmp3Real n low (b:ℝ)+(n.highFee:ℝ) < 49/100-(Kgraph:ℝ)*b
  weak_cap : ((low.B:ℝ)*sourceF3Real n low (b:ℝ)-sourceTReal n (b:ℝ))/(low.L:ℝ) ≤
    (low.cap:ℝ)*sourceF3Real n low (b:ℝ)
  cell : 2*((b:ℝ)-2*(n.allowance:ℝ)) ≤ sourceF3Real n low (b:ℝ)-(n.allowance:ℝ)
  mixed_payment : n.lowFee*(1-6*n.q*(low.B/low.L))+sourceD n low b*(1+n.q-6*n.q*(low.B/low.L)) =
    n.q*sourceX0 n low b+n.lowFee
  -- the nodes `vnode2 n low b δ θ`, `0 ≤ θ ≤ δ ≤ d`, at the width `b - θ`
  node_T : ∀ δ θ : ℚ, sourceTReal (vnode2 n low b δ θ) ((b-θ:ℚ):ℝ) = sourceTReal n (b:ℝ)
  node_amp : ∀ δ θ : ℚ, sourceAReal (vnode2 n low b δ θ) low ((b-θ:ℚ):ℝ) = (n.lowFee:ℝ)+(δ:ℝ)
  node_F : ∀ δ θ : ℚ, sourceFReal (vnode2 n low b δ θ) low ((b-θ:ℚ):ℝ) = 1-6*(n.lowFee:ℝ)-6*(δ:ℝ)
  node_low : ∀ δ θ : ℚ, 0≤θ → θ≤δ → δ≤sourceD n low b →
    RealGeometryLow (vnode2 n low b δ θ) low ((b-θ:ℚ):ℝ)
  node_shape : ∀ δ θ : ℚ, 0≤θ →
    (vnode2 n low b δ θ).B ≤ 1 ∧ 1 < (vnode2 n low b δ θ).L ∧ (vnode2 n low b δ θ).cap < 1
  price_frozen : ∀ δ θ : ℚ, 0≤θ → θ≤δ → δ≤sourceD n low b → ∀ ε : ℝ, 0≤ε → ε≤6*(n.allowance:ℝ) →
    MixedNodePrice (vnode2 n low b δ θ) low ((b-θ:ℚ):ℝ) (((b-θ:ℚ):ℝ)-ε)
  price_top : ∀ θ : ℚ, 0≤θ → θ≤sourceD n low b →
    (n.q:ℝ)*((sourceD n low b:ℝ)-θ) ≤ 6*(n.allowance:ℝ) →
    MixedNodePrice (vnode2 n low b (sourceD n low b) θ) low ((b-θ:ℚ):ℝ) 0
  gaps : ∀ δ θ : ℚ, 0≤θ → θ≤δ → δ≤sourceD n low b → ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
    QRH.RepeatedMarks.Source.ActualGapsK (vnode2 n low b δ θ) low h ((b-θ:ℚ):ℝ) ν reserve
  gaps_rm : ∀ δ θ : ℚ, 0≤θ → θ≤δ → δ≤sourceD n low b → ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
    ActualGaps_rm (vnode2 n low b δ θ) low (some h) ((b-θ:ℚ):ℝ) ν reserve

/-- **The ledger from the certificates.** One reserve, chosen before the width. -/
theorem mixed_geometry_of_valid3 (n low h : Source) (hv : SourceValid3 n low h)
    (hX : SourceValid3X n low) (hlow : ParentGood low) (he : 0 < (n.allowance:ℝ)) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b : ℚ, (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ) →
      MixedGeometry (9/2) n low h b reserve := by
  have hC := hv.1
  have S := shape3_of n low h hC
  have hL0q : (0:ℚ) < low.L := lt_trans (by norm_num) hlow.2.2.1
  have hden := sourceDen_ne_of_valid3X hX hL0q
  have hdenneg := sourceDen_neg_of_valid3X hX hL0q
  obtain ⟨reserve, hr, hgaps⟩ := mixed_uniform_reserve n low h hv hlow hden he.le
  refine ⟨reserve, hr, ?_⟩
  intro b hb
  have hgood := hC.2.2.2.2.2.2.2.2.2.2.2.1
  have hall := scalar3_full_width n low h hC hb
  have hg := hall.1
  have g0 := hg 0; have g1 := hg 1; have g2 := hg 2; have g3 := hg 3; have g4 := hg 4
  have g5 := hg 5; have g6 := hg 6; have g7 := hg 7; have g8 := hg 8; have g9 := hg 9
  have g10 := hg 10; have g11 := hg 11; have g12 := hg 12; have g13 := hg 13
  have g14 := hg 14; have g15 := hg 15; have g16 := hg 16
  simp only [scalarGate3Real] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16
  norm_num at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16
  have hd0 := sourceD_nonneg n low h hC hlow he.le hb
  have hq0 : (0:ℝ) ≤ n.q := by linarith [S.q_half]
  have hq1 : (n.q:ℝ) ≤ 1 := by linarith [S.q_lt]
  -- the cell condition on the whole cell (CellRatio3 at the two endpoints)
  have hcr : 2*((b:ℝ) - 2*(n.allowance:ℝ)) ≤ sourceF3Real n low (b:ℝ) - (n.allowance:ℝ) := by
    have hl := hv.2.2 (crossing n low) (by simp)
    have hr' := hv.2.2 n.cap (by simp)
    have haff : WidthAffine (fun x : ℝ => sourceF3Real n low x - (n.allowance:ℝ) -
        2*(x - 2*(n.allowance:ℝ))) := by
      intro x y t
      simp only [sourceF3Real, sourceDReal, sourceTReal]; ring
    have hf (c : ℚ) (hc' : 2*(c - 2*n.allowance) ≤ sourceF3 n low c - n.allowance) :
        0 ≤ sourceF3Real n low (c:ℝ) - (n.allowance:ℝ) - 2*((c:ℝ) - 2*(n.allowance:ℝ)) := by
      rw [sourceF3Real_rat]
      have hh : ((2*(c - 2*n.allowance) : ℚ) : ℝ) ≤ ((sourceF3 n low c - n.allowance : ℚ) : ℝ) := by
        exact_mod_cast hc'
      push_cast at hh
      linarith
    have := width_affine_nonnegative haff hb (hf _ hl) (hf _ hr')
    linarith
  refine
    { parent := ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1⟩
      low_parent := hlow
      high_parent := ?_
      q_half := S.q_half
      q_lt := S.q_lt
      allowance_pos := he
      den_ne := hden
      den_neg := hdenneg
      den3_pos := by exact_mod_cast g0
      width_mem := hb
      reserve_pos := hr
      d_rat := sourceDReal_rat n low b
      d_nonneg := hd0
      fee_pos := by exact_mod_cast g2
      live_room := by linarith
      amp_small := by simp only [sourceAmp3Real]; linarith
      raw_factor_room := by linarith
      parent_budget_room := by linarith
      qcap_room := by linarith
      low_fee_room := by linarith
      fee_allowance := by linarith
      reference_pos := by push_cast; linarith
      reference_gap := by push_cast; linarith
      centered_twin := by simp only [sourceAmp3Real]; push_cast; linarith
      zero_twin := by simp only [sourceAmp3Real]; linarith
      second_tail := by simp only [sourceAmp3Real]; linarith
      mixed_tail := by simp only [sourceAmp3Real]; linarith
      reference_tail := by simp only [sourceAmp3Real]; push_cast; linarith
      weak_cap := by have := hall.2; simp only [weakCap3Real] at this; linarith
      cell := hcr
      mixed_payment := mixed_payment n low b (by exact_mod_cast (ne_of_gt g0)) (ne_of_gt hL0q)
      node_T := fun δ θ => vnode2R_T n low b δ θ
      node_amp := fun δ θ => vnode2R_A n low b δ θ hden
      node_F := fun δ θ => vnode2R_F n low b δ θ hden
      node_low := fun δ θ hθ0 hθ hδ =>
        realGeometryLow_vnode2 n low h hC hlow hden he.le hb hθ0 hθ hδ
      node_shape := fun δ θ hθ0 => vnode2_shape n low h hC hθ0
      price_frozen := fun δ θ hθ0 hθ hδ ε hε0 hε =>
        mixed_node_price_frozen n low h hC hlow hden he.le hb hθ0 hθ hδ hε0 hε
      price_top := fun θ hθ0 hθ hslack =>
        mixed_node_price_top n low h hC hlow hden he.le hb hθ0 hθ hslack
      gaps := fun δ θ hθ0 hθ hδ ν hν => hgaps b hb δ θ hθ0 hθ hδ ν hν
      gaps_rm := fun δ θ hθ0 hθ hδ ν hν =>
        QRH.Record1252270103Source.PhysicalScalar.actualGaps_rm_of_K (hgaps b hb δ θ hθ0 hθ hδ ν hν) }
  -- the HIGH parent's shape
  obtain ⟨hB0, hB1, hL, hc0, hc1⟩ := hgood
  refine ⟨?_, by exact_mod_cast hB1, by exact_mod_cast hL, by exact_mod_cast hc0,
    by exact_mod_cast hc1.le⟩
  have hh := (Rat.cast_le (K:=ℝ)).mpr hB0
  norm_num at hh
  exact hh

/-! ## The gate list (N7)

Beyond `SourceValid3` the downstream needs only `SourceValid3X` (`0 < 6qB₀ - Λ₀`). Each candidate of
the design, with its status:
* MAIN twins `T + 5(a+d) + fee < 1` and `T + 9(a+d) + fee < 5/6 + 0.499·Lref`: scalar gates 12 and 11
  of `SourceValid3` (`MixedGeometry.zero_twin`, `MixedGeometry.centered_twin`).
* §1d pool-only gate `r(1-6qβ) + q(1-1/Λ₀)f ≥ qX₀ + r` for `f ≥ b - s`, `s(Λ₀-1) ≤ 4e`:
  from scalar gate 5 and `d ≥ 0` (`pool_only_gate`).
* `mesh < r/2`: a choice; it gives `mesh < a_v/2` at every node (`vnode2_amp_ge`).
* grid uniformity: a choice (`g, δw, κ` with `δw + g + κ ≤ ε ≤ 6e`; top node at `d`).
* the weak cap at the node scale `1 - 6r - 6δ` for `δ < d`: NOT implied (false at `δ = 0` on fan
  step 1); not needed, since the frozen price does not use it.
* `ParentGood (vnode2 …)` (i.e. `0 < n.B - n.L·θ`): NOT implied; not needed (only `1 < n.L` is used). -/

theorem main_twins_of_valid3 (n low h : Source) (hv : SourceValidC3 n low h) {b : ℝ}
    (hb : b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    sourceTReal n b+b+5*sourceAmp3Real n low b+(n.highFee:ℝ) < 1 ∧
    sourceTReal n b+b+9*sourceAmp3Real n low b+(n.highFee:ℝ) < 5/6+(499/1000)*(49/100-(9/2)*b) := by
  have hg := (scalar3_full_width n low h hv hb).1
  have g11 := hg 11
  have g12 := hg 12
  simp only [scalarGate3Real] at g11 g12
  norm_num at g11 g12
  constructor <;> simp only [sourceAmp3Real] <;> linarith

end
end QRH.MixedStep.Ledger
#print axioms QRH.MixedStep.Ledger.mixed_geometry_of_valid3
#print axioms QRH.MixedStep.Ledger.activeWidthGrid_rat
#print axioms QRH.MixedStep.Ledger.main_twins_of_valid3
