/- Mixed step (N7): the NF source step of the mixed chain, `NFStep3`. Fork of Collet's `nf_truncated`
(Core/InitialRegularCallbacks.lean) and `regular_meshes_from_sources`
(High/GlobalPhysicalRegularMesh.lean), through PR 76's `nf_truncated2` (`Source/NFStep2.lean`).

Changes, for a mixed step (`SourceValid3`, two parents, node grid):
* The reserve and the first layer come from `mixed_geometry_of_valid3` (`MixedGeometry`; no
  `RealGeometry`). `σ` and the HIGH budget `θ` (`FixedBudget σ 100 100 1 θ`, so `θ < σ/256`) come
  from Collet's `fixed_regular_setup` at `min reserve step`, as in `regular_meshes_from_sources`.
* One rational `q₀ ≤ min (θ/2) (2e)` is the width delta, the grid step and the grid slack:
  `δw = g = κ = q₀`, frozen slack `εf = 3q₀ ≤ 6e`, so `δw + κ ≤ θ` and `δw + g + κ ≤ εf`.
  The width grid is rational (`activeWidthGrid_rat`). For each grid width `b`, the node grid is
  `G = ⟨q₀, q₀, sourceD n low b⟩` and the frozen margin is `mixedPhi G b εf` (`0` at the top node,
  `(b - θ(δ)) - εf` below it): the ledger's `price_top` and `price_frozen`.
* The mesh is below the node LOW meshes (`regularLowMesh_mx` at every node of `G`), `r/4`, `θ/100`,
  `q₀/2`, `d/2` (if `d > 0`) and the HIGH parent mesh; `ξ ≤ min θ step`.
* The two suppliers are hypotheses with their owners' statements: `RegularSupplier3Holds` (the fork
  lead's `regular_supplier3`, `Downstream/Contract3.lean`) and `BalancedOfRegular3Statement` (the
  N3/N6 agent's `balanced_of_regular3`, `Downstream/Balanced3.lean`), and the latter's hypothesis
  `PlainTransfer` (`Downstream/Families.lean`).
* Collet's `truncated_of_balanced` is replaced by `truncated_of_balanced_mx`, which reads only
  `MixedGeometry.reference_pos`. -/
import Submissions.arvi_mixed_step.Source.NFPhysical3
import Submissions.arvi_mixed_step.Downstream.Contract3
import Submissions.arvi_mixed_step.Downstream.MainGates
import Submissions.arvi_mixed_step.Downstream.Families
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.InitialBalancedToTruncated
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularSetup
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PhysicalReserveK

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.MixedStep.Source
noncomputable section
open OAI.SevenEighths Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record1252270103Low QRH.Record1252270103Source QRH.Record1252270103Source.InitialTruncated
open QRH.Record1252270103Source.FixedWidthPhysical QRH.Record1252270103Source.PhysicalAnalytic
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Source.InitialRegularToTruncated
open QRH.MixedStep.Finite QRH.MixedStep.Ledger QRH.MixedStep.Downstream

/-! ## The two supplier statements -/

/-- The statement of the fork lead's `regular_supplier3` (`Downstream/Contract3.lean`), for all
arguments. -/
def RegularSupplier3Holds : Prop :=
  ∀ (K:ℚ) (n low high:Source) (b:ℚ) (reserve θ mesh ξ width:ℝ) (G:NodeGrid) (φ:ℚ→ℝ),
    RegularSupplier3Statement K n low high b reserve θ mesh ξ width G φ

/-- The statement of the N3/N6 agent's `balanced_of_regular3` (`Downstream/Balanced3.lean`;
provisional statement of 2026-10-26, copied verbatim). -/
def BalancedOfRegular3Statement : Prop :=
  ∀ (K:ℚ) (n low:Source) (b:ℚ) (mesh ξ reserve width:ℝ) (G:NodeGrid) (φ:ℚ→ℝ) (Amix F εf:ℝ),
    MainTwinFacts K n low (b:ℝ) (n.lowFee:ℝ) Amix F (2*mesh) →
    (n.lowFee:ℝ)+(G.d:ℝ)≤Amix → Amix<1/75 →
    (n.B:ℝ)≤1 → 1≤(n.L:ℝ) → (n.cap:ℝ)≤1 →
    0<(n.allowance:ℝ) → 0≤(n.highFee:ℝ) →
    0<mesh → mesh<(n.lowFee:ℝ)/2 →
    2*mesh≤(G.g:ℝ) → 2*mesh≤(G.κ:ℝ) → (0<G.d→2*mesh≤(G.d:ℝ)) →
    width+G.g+G.κ≤εf → φ G.d≤0 →
    (∀δ∈G.nodes,δ≠G.d→φ δ≤(b:ℝ)-G.theta δ-εf) →
    0<ξ → ξ≤1 → ξ≤PhysicalLowGuard.step n →
    0≤reserve → reserve≤1 → reserve≤PhysicalLowGuard.step n →
    width≤PhysicalLowGuard.step n →
    PlainTransfer →
    RegularJointSupplier3 K n low b mesh ξ reserve width G φ →
    BalancedInitialSupplier K n low (b:ℝ) mesh ξ width

/-! ## The node facts of the grid -/

/-- The frozen margin of the grid: `0` at the top node `d`, `(b - θ(δ)) - εf` below it. -/
def mixedPhi (G : NodeGrid) (b : ℚ) (εf : ℝ) (δ : ℚ) : ℝ :=
  if δ = G.d then 0 else ((b - G.theta δ : ℚ) : ℝ) - εf

/-- A finite family of positive numbers has a positive lower bound. -/
theorem exists_pos_le_finset (S : Finset ℚ) (f : ℚ → ℝ) (hf : ∀ δ ∈ S, 0 < f δ) :
    ∃ m : ℝ, 0 < m ∧ ∀ δ ∈ S, m ≤ f δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨m, hm, hle⟩ := ih (fun δ hδ => hf δ (Finset.mem_insert_of_mem hδ))
    refine ⟨min m (f a), lt_min hm (hf a (Finset.mem_insert_self a s)), ?_⟩
    intro δ hδ
    rcases Finset.mem_insert.mp hδ with rfl | hδ
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle δ hδ)

/-- The prices at the nodes of the grid: `price_top` at `d`, `price_frozen` below it. -/
theorem mixed_node_prices {Kgraph : ℚ} {n low h : Source} {b : ℚ} {reserve : ℝ}
    (hg : MixedGeometry Kgraph n low h b reserve) (G : NodeGrid) (hGd : G.d = sourceD n low b)
    (hq1 : (n.q:ℝ) ≤ 1) (hκ : (G.κ:ℝ) ≤ 6*(n.allowance:ℝ)) (εf : ℝ) (hε0 : 0 ≤ εf)
    (hε : εf ≤ 6*(n.allowance:ℝ)) :
    ∀ δ ∈ G.nodes, MixedNodePrice (vnode2 n low b δ (G.theta δ)) low ((b - G.theta δ : ℚ) : ℝ)
      (mixedPhi G b εf δ) := by
  intro δ hδ
  by_cases htop : δ = G.d
  · subst htop
    have hφ : mixedPhi G b εf G.d = 0 := by simp [mixedPhi]
    rw [hφ]
    have hslack := G.top_slack (n.q:ℝ) (n.allowance:ℝ) hq1 hκ
    have hslack' : (n.q:ℝ)*((sourceD n low b:ℝ)-(G.theta G.d:ℝ)) ≤ 6*(n.allowance:ℝ) := by
      have e1 : ((sourceD n low b : ℚ) : ℝ) = ((G.d : ℚ) : ℝ) := by rw [hGd]
      rw [e1]
      exact hslack
    have h1 := hg.price_top (G.theta G.d) (G.theta_nonneg _)
      ((G.theta_le G.d_nonneg).trans_eq hGd) hslack'
    rw [← hGd] at h1
    exact h1
  · have hφ : mixedPhi G b εf δ = ((b - G.theta δ : ℚ) : ℝ) - εf := by simp [mixedPhi, htop]
    rw [hφ]
    exact hg.price_frozen δ (G.theta δ) (G.theta_nonneg δ) (G.theta_le (G.node_nonneg hδ))
      ((G.node_le_top hδ).trans_eq hGd) εf hε0 hε

/-- The node geometry at the nodes of the grid (`RealGeometryLow` and the node shape). -/
theorem mixed_node_geometry {Kgraph : ℚ} {n low h : Source} {b : ℚ} {reserve : ℝ}
    (hg : MixedGeometry Kgraph n low h b reserve) (G : NodeGrid) (hGd : G.d = sourceD n low b) :
    ∀ δ ∈ G.nodes, NodeGeometry_mx (vnode2 n low b δ (G.theta δ)) low ((b - G.theta δ : ℚ) : ℝ) := by
  intro δ hδ
  have hθ0 := G.theta_nonneg δ
  have hrl := hg.node_low δ (G.theta δ) hθ0 (G.theta_le (G.node_nonneg hδ))
    ((G.node_le_top hδ).trans_eq hGd)
  obtain ⟨hB, hL, hc⟩ := hg.node_shape δ (G.theta δ) hθ0
  exact ⟨hrl.lowL_pos, hrl.a_pos, hrl.a_small, hrl.a_allowance, hrl.parent_budget_room, hB, hL, hc⟩

/-- The actual HIGH gaps at the nodes of the grid, at any `σ ≤ reserve`. -/
theorem mixed_node_gaps {Kgraph : ℚ} {n low h : Source} {b : ℚ} {reserve σ : ℝ}
    (hg : MixedGeometry Kgraph n low h b reserve) (G : NodeGrid) (hGd : G.d = sourceD n low b)
    (hσ : σ ≤ reserve) :
    ∀ δ ∈ G.nodes, ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
      QRH.Record1252270103Source.PhysicalScalar.ActualGaps_rm (vnode2 n low b δ (G.theta δ)) low
        (some h) ((b - G.theta δ : ℚ) : ℝ) ν σ := by
  intro δ hδ ν hν
  exact QRH.Record1252270103Source.PhysicalScalar.actualGaps_rm_of_K
    (QRH.RepeatedMarks.Source.actualGapsK_mono hσ
      (hg.gaps δ (G.theta δ) (G.theta_nonneg δ) (G.theta_le (G.node_nonneg hδ))
        ((G.node_le_top hδ).trans_eq hGd) ν hν))

/-! ## The truncated layer -/

/-- **The truncated layer of a mixed step** (Collet's `nf_truncated`, PR 76's `nf_truncated2`,
mixed), from the two suppliers. The parameters are chosen in the order reserve, `σ` and `θ`,
the width delta and the grid, then (for each grid width) the node prices, the mesh and `ξ`. -/
theorem nf_truncated3_of (hreg : RegularSupplier3Holds) (hbal : BalancedOfRegular3Statement)
    (htr : PlainTransfer) (n low h : Source) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hK : 6*(2*HeckeZeroSupremum.beta-1) ≤ QRH.RepeatedMarks.natK)
    (hv : SourceValid3 n low h) (hX : SourceValid3X n low) (hlow : ParentGood low)
    (ha : NFAccounting n) (hG : P low) (hGH : P h) :
    ∃ δw : ℝ, 0 < δw ∧ MixedTruncatedAt n low δw := by
  have hn : ParentGood n := QRH.MixedStep.Graph.parent_good_of_valid3 hv
  have hG' : GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ) := hG
  have hallow : 0 < (n.allowance:ℝ) := by exact_mod_cast (nf_accounting_positive ha).1
  have hfee0 : 0 ≤ (n.highFee:ℝ) := by exact_mod_cast (nf_accounting_positive ha).2.2.le
  have hβhi : HeckeZeroSupremum.beta ≤ 7/8 := by
    have h1 := hK
    unfold QRH.RepeatedMarks.natK at h1
    linarith
  have hL0 : 0 ≤ (n.L:ℝ) := by
    have h1 : (1:ℝ) < n.L := by exact_mod_cast hn.2.2.1
    linarith
  have hstep : 0 < PhysicalLowGuard.step n := by unfold PhysicalLowGuard.step; positivity
  have hcap1 : (n.cap:ℝ) < 1 := by exact_mod_cast hn.2.2.2.2
  obtain ⟨hB0, hB1, hlam, hc0, hc1⟩ := hv.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hB0' : (22/23:ℝ) ≤ (h.B:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hB0
    norm_num at hh
    exact hh
  -- the reserve, before every width
  obtain ⟨reserve, hr, hgeo⟩ := mixed_geometry_of_valid3 n low h hv hX hlow hallow
  -- `σ` and the HIGH budget `θ`, before every width
  obtain ⟨σ, θ, _outer, _hσ, hσr, hσa, hf, _houter, _hwidth, _hceil⟩ :=
    fixed_regular_setup n (min reserve (PhysicalLowGuard.step n)) (lt_min hr hstep) hallow hL0
  have hθ0 : 0 < θ := hf.positive
  have hθstep : θ ≤ PhysicalLowGuard.step n := by
    have hs := hσr.trans (min_le_right _ _)
    linarith only [hf.tiny, hf.positive, hs]
  have hσres : σ ≤ reserve := hσr.trans (min_le_left _ _)
  have hθsmall : θ ≤ 1/100000 := hf.small
  -- the HIGH parent mesh
  obtain ⟨mh, hmh, hhigh⟩ := selected_high_parent_mesh (some h) θ hθ0 (by
    intro h' hh'
    simp only [Option.mem_def, Option.some.injEq] at hh'
    subst hh'
    exact hGH)
  -- the width delta, the grid step and the grid slack: one rational `q₀`
  obtain ⟨q0, hq0, hq0le⟩ := exists_rat_width_delta (min (θ/2) (2*(n.allowance:ℝ)))
    (lt_min (by linarith) (by linarith))
  have hq0θ : (q0:ℝ) ≤ θ/2 := hq0le.trans (min_le_left _ _)
  have hq0e : (q0:ℝ) ≤ 2*(n.allowance:ℝ) := hq0le.trans (min_le_right _ _)
  have hq0' : (0:ℝ) < q0 := by exact_mod_cast hq0
  refine ⟨q0, hq0', ?_⟩
  intro ε _hε b hb
  obtain ⟨bq, rfl, hbI⟩ := activeWidthGrid_rat (crossing n low) n.cap q0 hb
  have hg := hgeo bq hbI
  -- the node grid and the frozen margin at the width `bq`
  obtain ⟨G, hGg, hGκ, hGd⟩ : ∃ G : NodeGrid, G.g = q0 ∧ G.κ = q0 ∧ G.d = sourceD n low bq :=
    ⟨⟨q0, q0, sourceD n low bq, hq0, hq0.le, hg.d_nonneg⟩, rfl, rfl, rfl⟩
  have hGg' : (G.g:ℝ) = q0 := by rw [hGg]
  have hGκ' : (G.κ:ℝ) = q0 := by rw [hGκ]
  have hq1 : (n.q:ℝ) ≤ 1 := by linarith [hg.q_lt]
  have hprice := mixed_node_prices hg G hGd hq1 (by rw [hGκ']; linarith) (3*(q0:ℝ))
    (by linarith) (by linarith)
  -- the node LOW meshes
  obtain ⟨Lmin, hLmin, hLle⟩ := exists_pos_le_finset G.nodes
    (fun δ => if hδ : δ ∈ G.nodes then
      regularLowMesh_mx (vnode2 n low bq δ (G.theta δ)) low ((bq - G.theta δ : ℚ) : ℝ)
        (mixedPhi G bq (3*(q0:ℝ)) δ) θ (hprice δ hδ) hlow hallow hg.q_half hq1 hG' hθ0
    else 1)
    (by
      intro δ hδ
      simp only [hδ, ↓reduceDIte]
      exact regular_low_mesh_positive_mx _ _ _ _ _ _ _ _ _ _ _ _)
  -- the top-node mesh
  obtain ⟨md, hmd, hmdd⟩ : ∃ md : ℝ, 0 < md ∧ ∀ mesh : ℝ, mesh ≤ md → 0 < G.d →
      2*mesh ≤ (G.d:ℝ) := by
    by_cases hd0 : (0:ℚ) < G.d
    · have hd0' : (0:ℝ) < (G.d:ℝ) := by exact_mod_cast hd0
      exact ⟨(G.d:ℝ)/2, by linarith, fun mesh hm _ => by linarith⟩
    · exact ⟨1, one_pos, fun mesh _ hd => absurd hd hd0⟩
  have hr0 : 0 < (n.lowFee:ℝ) := hg.fee_pos
  refine ⟨min (min (min Lmin ((n.lowFee:ℝ)/4)) (min (θ/100) ((q0:ℝ)/2))) (min md (mh/100)),
    min θ (PhysicalLowGuard.step n),
    lt_min (lt_min (lt_min hLmin (by linarith)) (lt_min (by linarith) (by linarith)))
      (lt_min hmd (by linarith)),
    lt_min hθ0 hstep, ?_⟩
  intro mesh ξ hm0 hmm hx0 hxx
  have hmL : mesh ≤ Lmin :=
    hmm.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hmr : mesh ≤ (n.lowFee:ℝ)/4 :=
    hmm.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hmθ : mesh ≤ θ/100 :=
    hmm.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hmq : mesh ≤ (q0:ℝ)/2 :=
    hmm.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmmd : mesh ≤ md := hmm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmh' : mesh ≤ mh/100 := hmm.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hxθ : ξ ≤ θ := hxx.trans (min_le_left _ _)
  have hxstep : ξ ≤ PhysicalLowGuard.step n := hxx.trans (min_le_right _ _)
  -- the residual regular inlet (fork lead)
  have hnodes : ∀ δ ∈ G.nodes, NodeFacts3 n low h bq σ θ mesh G (mixedPhi G bq (3*(q0:ℝ)))
      hlow hallow hg.q_half hq1 hG' hθ0 δ := by
    intro δ hδ
    refine ⟨hprice δ hδ, mixed_node_geometry hg G hGd δ hδ, mixed_node_gaps hg G hGd hσres δ hδ, ?_⟩
    have hl := hLle δ hδ
    simp only [hδ, ↓reduceDIte] at hl
    exact hmL.trans hl
  have hreg3 : RegularJointSupplier3 (9/2) n low bq mesh ξ θ (q0:ℝ) G (mixedPhi G bq (3*(q0:ℝ))) :=
    hreg (9/2) n low h bq σ θ mesh ξ (q0:ℝ) G (mixedPhi G bq (3*(q0:ℝ))) hf hm0.le (by linarith)
      hx0 hxθ hσa hfee0 hallow hg.q_half hq1 hn hlow hG' hβ hβhi hg.den_ne hg.reference_pos
      (hbI.2.trans hcap1.le) hr0 (by linarith) hθstep hq0'.le (by rw [hGκ']; linarith) hB0'
      (by exact_mod_cast hB1) (by exact_mod_cast hlam) (by exact_mod_cast hc0)
      (by exact_mod_cast hc1) (hhigh (100*mesh) (by linarith)) hnodes
  -- the balanced supplier (N3/N6 agent)
  have htw := mainTwinFacts_of_mixedGeometry hg hv.1 hX (2*mesh) (by linarith) (by linarith)
  have hAd : (n.lowFee:ℝ) + (G.d:ℝ) ≤ sourceAmp3Real n low (bq:ℝ) := by
    have e1 : sourceAmp3Real n low (bq:ℝ) = (n.lowFee:ℝ) + sourceDReal n low (bq:ℝ) := rfl
    exact le_of_eq (by rw [e1, hg.d_rat, hGd])
  have hφtop : mixedPhi G bq (3*(q0:ℝ)) G.d ≤ 0 :=
    (show mixedPhi G bq (3*(q0:ℝ)) G.d = 0 by simp [mixedPhi]).le
  have hφ : ∀ δ ∈ G.nodes, δ ≠ G.d →
      mixedPhi G bq (3*(q0:ℝ)) δ ≤ (bq:ℝ) - G.theta δ - 3*(q0:ℝ) := by
    intro δ _ hne
    have e1 : mixedPhi G bq (3*(q0:ℝ)) δ = ((bq - G.theta δ : ℚ) : ℝ) - 3*(q0:ℝ) := by
      simp [mixedPhi, hne]
    rw [e1]
    push_cast
    exact le_rfl
  have hbal3 : BalancedInitialSupplier (9/2) n low (bq:ℝ) mesh ξ (q0:ℝ) :=
    hbal (9/2) n low bq mesh ξ θ (q0:ℝ) G (mixedPhi G bq (3*(q0:ℝ))) (sourceAmp3Real n low (bq:ℝ))
      (sourceF3Real n low (bq:ℝ)) (3*(q0:ℝ)) htw hAd hg.amp_small (by exact_mod_cast hv.1.2.1)
      (by exact_mod_cast hv.1.2.2.1.le) (by exact_mod_cast hv.1.2.2.2.2.1.le) hallow hfee0 hm0
      (by linarith) (by rw [hGg']; linarith) (by rw [hGκ']; linarith)
      (fun hd0 => hmdd mesh hmmd hd0) (by rw [hGg', hGκ']; linarith) hφtop hφ hx0
      (by linarith) hxstep hθ0.le (by linarith) hθstep (by linarith) htr hreg3
  -- the truncated supplier
  have htrunc := truncated_of_balanced_mx (9/2) n low (bq:ℝ) mesh ξ (q0:ℝ) hg.reference_pos hbal3
  have hcast : ((9/2:ℚ):ℝ) = QRH.RepeatedMarks.natK := by norm_num [QRH.RepeatedMarks.natK]
  exact Eq.mp (congrArg (fun κ:ℝ => FixedSubsetTruncatedSupplier (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)
    (crossing n low:ℝ) κ mesh ξ 0 (bq:ℝ) (q0:ℝ)) hcast) htrunc

/-! ## The source step -/

/-- **The mixed source step from the two suppliers** (and the plain-family transfer contract). -/
theorem nf_step3_of (hreg : RegularSupplier3Holds) (hbal : BalancedOfRegular3Statement)
    (htr : PlainTransfer) : QRH.MixedStep.Graph.NFStep3 := by
  intro n low h hβ hK hv hX hlow ha hp hph
  obtain ⟨δw, hδ, htrunc⟩ := nf_truncated3_of hreg hbal htr n low h hβ hK hv hX hlow ha hp hph
  exact nf_step3_of_truncated n low h hβ hK hv hlow hp δw hδ htrunc

end
end QRH.MixedStep.Source
#print axioms QRH.MixedStep.Source.exists_pos_le_finset
#print axioms QRH.MixedStep.Source.mixed_node_prices
#print axioms QRH.MixedStep.Source.mixed_node_geometry
#print axioms QRH.MixedStep.Source.mixed_node_gaps
#print axioms QRH.MixedStep.Source.nf_truncated3_of
#print axioms QRH.MixedStep.Source.nf_step3_of
