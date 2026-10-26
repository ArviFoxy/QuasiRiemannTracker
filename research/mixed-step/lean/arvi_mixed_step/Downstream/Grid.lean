/- Mixed source step, N3 (pieces): new in this submission. Uses Sil's `upward_subset` (vendored in
PR 76, `FourthPower/GlobalSlotSelection.lean`) by import; no code is adapted.

The node grid and the windowed greedy block (`L45_DESIGN.md` §2.2, `LEDGER_INTERFACE.md` v3 §0).

* `NodeGrid`: a grid step `g > 0`, the slack `κ ≥ 0` of the B/width shift, and the top node
  `d ≥ 0` (for the transfer: `d = sourceD n low b`). All rational and fixed before `Z`.
* `NodeGrid.nodes = {k·g : k·g < d} ∪ {d}`, a `Finset ℚ`.
* `NodeGrid.nodeOf x`: the node of a piece of transferable width `x`: `d` if `d ≤ x`, else `⌊x/g⌋·g`.
  `NodeGrid.theta δ = max 0 (δ − κ)`: the B/width shift `θ` of the ledger's `vnode2 n low b δ θ`.
* `frozen_obligation`: at a non-top node (`x < d`) the piece has `x < δ + g`; so `b − δw ≤ f + x`
  and `δw + g + κ ≤ ε` give `(b − θ) − ε ≤ f` (the hypothesis of `mixed_node_price_frozen`).
* `top_slack`: at the top node `q·(d − θ) ≤ 6e` once `κ ≤ 6e`, `q ≤ 1` (`mixed_node_price_top`).
* `windowBlock T w δ mesh`: for a node `δ > 0` with `2·mesh ≤ δ` and `δ − 2·mesh ≤ Σ_T w`, a block
  `J ⊆ T` with `δ − 2·mesh ≤ Σ_J w ≤ δ − mesh` (Sil's `upward_subset`, as in the transfer's
  `select_block`, with target `δ − 2·mesh`); for `δ ≤ 0` it is `∅`. The window is the design's
  `[δ − 2·mesh, δ − η_Z]` with `η_Z := mesh` (so the block does not depend on `Z`); the radius
  condition of the transfer then needs only `log_Z(2·16^N) ≤ 6·mesh`.
* `pieceNode`, `pieceBlock`, `PieceFacts`: the node and block of a piece with transferable slots
  `T`, and every arithmetic fact about them used downstream. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.GlobalSlotSelection

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.MixedStep.Downstream
noncomputable section
open scoped BigOperators Classical

/-- The node grid (fixed before `Z`). -/
structure NodeGrid where
  g : ℚ
  κ : ℚ
  d : ℚ
  g_pos : 0 < g
  κ_nonneg : 0 ≤ κ
  d_nonneg : 0 ≤ d

namespace NodeGrid
variable (G : NodeGrid)

/-- The node of a piece of transferable width `x`. -/
def nodeOf (x : ℝ) : ℚ :=
  if (G.d : ℝ) ≤ x then G.d else (⌊x / (G.g : ℝ)⌋₊ : ℚ) * G.g

/-- The B/width shift at the node `δ`. -/
def theta (δ : ℚ) : ℚ := max 0 (δ - G.κ)

/-- The nodes `{k·g : k·g < d} ∪ {d}`. -/
def nodes : Finset ℚ :=
  insert G.d ((Finset.range ⌈G.d / G.g⌉₊).image (fun k : ℕ => (k : ℚ) * G.g))

theorem g_pos_real : (0 : ℝ) < G.g := by exact_mod_cast G.g_pos

theorem d_nonneg_real : (0 : ℝ) ≤ G.d := by exact_mod_cast G.d_nonneg

theorem κ_nonneg_real : (0 : ℝ) ≤ G.κ := by exact_mod_cast G.κ_nonneg

theorem nodeOf_top {x : ℝ} (h : (G.d : ℝ) ≤ x) : G.nodeOf x = G.d := by
  simp only [nodeOf, h, ↓reduceIte]

theorem nodeOf_low {x : ℝ} (h : x < G.d) : G.nodeOf x = (⌊x / (G.g : ℝ)⌋₊ : ℚ) * G.g := by
  simp only [nodeOf, not_le.mpr h, ↓reduceIte]

theorem nodeOf_low_real {x : ℝ} (h : x < G.d) :
    (G.nodeOf x : ℝ) = (⌊x / (G.g : ℝ)⌋₊ : ℝ) * (G.g : ℝ) := by
  rw [G.nodeOf_low h]
  push_cast
  ring

theorem nodeOf_nonneg (x : ℝ) : 0 ≤ G.nodeOf x := by
  unfold nodeOf
  split_ifs
  · exact G.d_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) G.g_pos.le

theorem nodeOf_le {x : ℝ} (hx : 0 ≤ x) : (G.nodeOf x : ℝ) ≤ x := by
  by_cases h : (G.d : ℝ) ≤ x
  · rw [G.nodeOf_top h]
    exact h
  · rw [G.nodeOf_low_real (not_le.mp h)]
    have hg := G.g_pos_real
    have hfl : (⌊x / (G.g : ℝ)⌋₊ : ℝ) ≤ x / G.g := Nat.floor_le (div_nonneg hx hg.le)
    calc (⌊x / (G.g : ℝ)⌋₊ : ℝ) * (G.g : ℝ) ≤ x / G.g * G.g :=
          mul_le_mul_of_nonneg_right hfl hg.le
      _ = x := div_mul_cancel₀ x hg.ne'

theorem lt_nodeOf_add {x : ℝ} (_hx : 0 ≤ x) (h : x < G.d) :
    x < (G.nodeOf x : ℝ) + G.g := by
  rw [G.nodeOf_low_real h]
  have hg := G.g_pos_real
  have hfl : x / G.g < (⌊x / (G.g : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1 : x = x / G.g * G.g := (div_mul_cancel₀ x hg.ne').symm
  calc x = x / G.g * G.g := h1
    _ < ((⌊x / (G.g : ℝ)⌋₊ : ℝ) + 1) * G.g := mul_lt_mul_of_pos_right hfl hg
    _ = (⌊x / (G.g : ℝ)⌋₊ : ℝ) * (G.g : ℝ) + G.g := by ring

theorem nodeOf_le_top {x : ℝ} (hx : 0 ≤ x) : G.nodeOf x ≤ G.d := by
  by_cases h : (G.d : ℝ) ≤ x
  · rw [G.nodeOf_top h]
  · have h1 := G.nodeOf_le hx
    have h2 : (G.nodeOf x : ℝ) ≤ G.d := h1.trans (not_le.mp h).le
    exact_mod_cast h2

theorem nodeOf_eq_top_iff {x : ℝ} (_hx : 0 ≤ x) : G.nodeOf x = G.d ↔ (G.d : ℝ) ≤ x := by
  constructor
  · intro he
    by_contra h
    have h1 := G.nodeOf_le _hx
    rw [he] at h1
    exact h h1
  · exact G.nodeOf_top

theorem mem_nodes {δ : ℚ} :
    δ ∈ G.nodes ↔ δ = G.d ∨ ∃ k : ℕ, (k : ℚ) * G.g < G.d ∧ δ = (k : ℚ) * G.g := by
  unfold nodes
  rw [Finset.mem_insert, Finset.mem_image]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, ?_, rfl⟩
    have hk' : (k : ℚ) < G.d / G.g := Nat.lt_ceil.mp (Finset.mem_range.mp hk)
    calc (k : ℚ) * G.g < G.d / G.g * G.g := mul_lt_mul_of_pos_right hk' G.g_pos
      _ = G.d := div_mul_cancel₀ _ G.g_pos.ne'
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, Finset.mem_range.mpr (Nat.lt_ceil.mpr ?_), rfl⟩
    rw [lt_div_iff₀ G.g_pos]
    exact hk

theorem nodeOf_mem {x : ℝ} (hx : 0 ≤ x) : G.nodeOf x ∈ G.nodes := by
  rw [G.mem_nodes]
  by_cases h : (G.d : ℝ) ≤ x
  · exact Or.inl (G.nodeOf_top h)
  · right
    refine ⟨⌊x / (G.g : ℝ)⌋₊, ?_, G.nodeOf_low (not_le.mp h)⟩
    have h1 : (G.nodeOf x : ℝ) < G.d := (G.nodeOf_le hx).trans_lt (not_le.mp h)
    rw [G.nodeOf_low (not_le.mp h)] at h1
    exact_mod_cast h1

theorem node_nonneg {δ : ℚ} (h : δ ∈ G.nodes) : 0 ≤ δ := by
  rcases G.mem_nodes.mp h with rfl | ⟨k, _, rfl⟩
  · exact G.d_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) G.g_pos.le

theorem node_le_top {δ : ℚ} (h : δ ∈ G.nodes) : δ ≤ G.d := by
  rcases G.mem_nodes.mp h with rfl | ⟨k, hk, rfl⟩
  · exact le_rfl
  · exact hk.le

/-- A positive node is at least `min g d`. -/
theorem node_pos_ge {δ : ℚ} (h : δ ∈ G.nodes) (h0 : δ ≠ 0) : min G.g G.d ≤ δ := by
  rcases G.mem_nodes.mp h with rfl | ⟨k, _, rfl⟩
  · exact min_le_right _ _
  · have hk : k ≠ 0 := by
      rintro rfl
      simp at h0
    have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    calc min G.g G.d ≤ G.g := min_le_left _ _
      _ = 1 * G.g := (one_mul _).symm
      _ ≤ (k : ℚ) * G.g := mul_le_mul_of_nonneg_right hk1 G.g_pos.le

/-- If `2·mesh ≤ g` and `2·mesh ≤ d` (when `d > 0`), every positive node is at least `2·mesh`. -/
theorem two_mesh_le_node {δ : ℚ} {mesh : ℝ} (h : δ ∈ G.nodes) (h0 : δ ≠ 0)
    (hg : 2 * mesh ≤ G.g) (hd : 0 < G.d → 2 * mesh ≤ G.d) : 2 * mesh ≤ δ := by
  have hm := G.node_pos_ge h h0
  have hdpos : 0 < G.d := lt_of_lt_of_le (lt_of_le_of_ne (G.node_nonneg h) (Ne.symm h0))
    (G.node_le_top h)
  have hm' : ((min G.g G.d : ℚ) : ℝ) ≤ δ := by exact_mod_cast hm
  rw [Rat.cast_min] at hm'
  exact (le_min hg (hd hdpos)).trans hm'

theorem theta_nonneg (δ : ℚ) : 0 ≤ G.theta δ := le_max_left _ _

theorem theta_le {δ : ℚ} (hδ : 0 ≤ δ) : G.theta δ ≤ δ :=
  max_le hδ (by linarith [G.κ_nonneg])

theorem sub_theta_le (δ : ℚ) : δ - G.theta δ ≤ G.κ := by
  have : δ - G.κ ≤ G.theta δ := le_max_right _ _
  linarith

theorem le_theta_add (δ : ℚ) : δ ≤ G.theta δ + G.κ := by
  have := G.sub_theta_le δ
  linarith

theorem theta_eq_zero {δ : ℚ} (h : δ ≤ G.κ) : G.theta δ = 0 :=
  max_eq_left (by linarith)

theorem theta_zero : G.theta 0 = 0 := G.theta_eq_zero G.κ_nonneg

/-- **Top slack**: `q·(d − θ(d)) ≤ 6e` (hypothesis of `mixed_node_price_top`). -/
theorem top_slack (q e : ℝ) (hq1 : q ≤ 1) (hκ : (G.κ : ℝ) ≤ 6 * e) :
    q * ((G.d : ℝ) - (G.theta G.d : ℝ)) ≤ 6 * e := by
  have h1 : (G.d : ℝ) - (G.theta G.d : ℝ) ≤ G.κ := by exact_mod_cast G.sub_theta_le G.d
  have h2 : 0 ≤ (G.d : ℝ) - (G.theta G.d : ℝ) := by
    have : G.theta G.d ≤ G.d := G.theta_le G.d_nonneg
    have : (G.theta G.d : ℝ) ≤ G.d := by exact_mod_cast this
    linarith
  calc q * ((G.d : ℝ) - (G.theta G.d : ℝ)) ≤ 1 * ((G.d : ℝ) - (G.theta G.d : ℝ)) :=
        mul_le_mul_of_nonneg_right hq1 h2
    _ ≤ 6 * e := by linarith

/-- **The frozen obligation** (`LEDGER_INTERFACE.md` §0.4). At a non-top node (`x < d`) the
transferable width is `x < δ + g`. With total width `b − δw ≤ f + x` and `δw + g + κ ≤ ε`, the
frozen width satisfies `(b − θ) − ε ≤ f`. -/
theorem frozen_obligation {x f b δw ε : ℝ} (hx : 0 ≤ x) (hlow : x < G.d)
    (hsum : b - δw ≤ f + x) (hε : δw + G.g + G.κ ≤ ε) :
    b - (G.theta (G.nodeOf x) : ℝ) - ε ≤ f := by
  have h1 := G.lt_nodeOf_add hx hlow
  have h2 : (G.nodeOf x : ℝ) ≤ (G.theta (G.nodeOf x) : ℝ) + G.κ := by
    exact_mod_cast G.le_theta_add (G.nodeOf x)
  linarith

end NodeGrid

/-! ### The windowed greedy block -/

section Window
variable {α : Type*}

/-- The windowed block: for `δ > 0`, a block `J ⊆ T` with `δ − 2·mesh ≤ Σ_J w ≤ δ − mesh`
(when one exists); for `δ ≤ 0`, the empty block. -/
def windowBlock (T : Finset α) (w : α → ℝ) (δ mesh : ℝ) : Finset α :=
  if h : 0 < δ ∧ ∃ J : Finset α, J ⊆ T ∧ δ - 2 * mesh ≤ ∑ j ∈ J, w j ∧ ∑ j ∈ J, w j ≤ δ - mesh
  then Classical.choose h.2 else ∅

theorem windowBlock_subset (T : Finset α) (w : α → ℝ) (δ mesh : ℝ) :
    windowBlock T w δ mesh ⊆ T := by
  unfold windowBlock
  split_ifs with h
  · exact (Classical.choose_spec h.2).1
  · exact Finset.empty_subset _

theorem windowBlock_of_nonpos (T : Finset α) (w : α → ℝ) {δ : ℝ} (mesh : ℝ) (hδ : δ ≤ 0) :
    windowBlock T w δ mesh = ∅ := by
  unfold windowBlock
  exact dite_eq_right_iff.mpr (fun h => absurd h.1 (not_lt.mpr hδ))

/-- The window: `δ − 2·mesh ≤ Σ_J w ≤ δ − mesh`. -/
theorem windowBlock_spec (T : Finset α) (w : α → ℝ) {δ mesh : ℝ} (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ T, 0 ≤ w i) (hwm : ∀ i ∈ T, w i ≤ mesh) (hδ : 0 < δ) (h2 : 2 * mesh ≤ δ)
    (hT : δ - 2 * mesh ≤ ∑ i ∈ T, w i) :
    δ - 2 * mesh ≤ ∑ j ∈ windowBlock T w δ mesh, w j ∧
      ∑ j ∈ windowBlock T w δ mesh, w j ≤ δ - mesh := by
  have hex : ∃ J : Finset α, J ⊆ T ∧ δ - 2 * mesh ≤ ∑ j ∈ J, w j ∧ ∑ j ∈ J, w j ≤ δ - mesh := by
    obtain ⟨R, hR, hlo, hhi⟩ := Candidate.FourthPower.GlobalSlotSelection.upward_subset T w
      (δ - 2 * mesh) mesh hm hw hwm (by linarith) hT
    exact ⟨R, hR, hlo, hhi.trans ((min_le_right _ _).trans (by linarith))⟩
  have h : 0 < δ ∧ ∃ J : Finset α, J ⊆ T ∧ δ - 2 * mesh ≤ ∑ j ∈ J, w j ∧
      ∑ j ∈ J, w j ≤ δ - mesh := ⟨hδ, hex⟩
  unfold windowBlock
  simp only [h]
  exact (Classical.choose_spec h.2).2

end Window

/-! ### The node and block of a piece -/

section Piece
variable {α : Type*}

/-- The node of a piece with transferable slots `T`. -/
def pieceNode (G : NodeGrid) (w : α → ℝ) (T : Finset α) : ℚ := G.nodeOf (∑ i ∈ T, w i)

/-- The transferred block of a piece with transferable slots `T`. -/
def pieceBlock (G : NodeGrid) (w : α → ℝ) (mesh : ℝ) (T : Finset α) : Finset α :=
  windowBlock T w (pieceNode G w T) mesh

theorem pieceBlock_subset (G : NodeGrid) (w : α → ℝ) (mesh : ℝ) (T : Finset α) :
    pieceBlock G w mesh T ⊆ T := windowBlock_subset _ _ _ _

/-- Every arithmetic fact about the node `δ`, the shift `θ` and the block `J` of a piece, with
`δ_act = Σ_J w` the transferred width. -/
structure PieceFacts (G : NodeGrid) (w : α → ℝ) (mesh : ℝ) (T : Finset α) : Prop where
  node_mem : pieceNode G w T ∈ G.nodes
  node_nonneg : 0 ≤ pieceNode G w T
  node_le_top : pieceNode G w T ≤ G.d
  theta_nonneg : 0 ≤ G.theta (pieceNode G w T)
  theta_le_node : G.theta (pieceNode G w T) ≤ pieceNode G w T
  block_subset : pieceBlock G w mesh T ⊆ T
  act_nonneg : 0 ≤ ∑ j ∈ pieceBlock G w mesh T, w j
  theta_le_act : (G.theta (pieceNode G w T) : ℝ) ≤ ∑ j ∈ pieceBlock G w mesh T, w j
  act_le_node : ∑ j ∈ pieceBlock G w mesh T, w j ≤ (pieceNode G w T : ℝ)
  shift : (pieceNode G w T : ℝ) - ∑ j ∈ pieceBlock G w mesh T, w j ≤ 2 * mesh
  node_le_trans : (pieceNode G w T : ℝ) ≤ ∑ i ∈ T, w i
  zero_or_window :
    (pieceNode G w T = 0 ∧ pieceBlock G w mesh T = ∅) ∨
      (0 < pieceNode G w T ∧ ∑ j ∈ pieceBlock G w mesh T, w j ≤ (pieceNode G w T : ℝ) - mesh)
  top_or_low :
    pieceNode G w T = G.d ∨
      ((∑ i ∈ T, w i) < G.d ∧ (∑ i ∈ T, w i) < (pieceNode G w T : ℝ) + G.g)

/-- The piece facts, under `0 ≤ w ≤ mesh`, `2·mesh ≤ g`, `2·mesh ≤ κ` and `2·mesh ≤ d` (if `d > 0`). -/
theorem pieceFacts (G : NodeGrid) (w : α → ℝ) {mesh : ℝ} (T : Finset α) (hm : 0 ≤ mesh)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh) (hg : 2 * mesh ≤ G.g)
    (hκ : 2 * mesh ≤ G.κ) (hd : 0 < G.d → 2 * mesh ≤ G.d) : PieceFacts G w mesh T := by
  have hx : 0 ≤ ∑ i ∈ T, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hmem : pieceNode G w T ∈ G.nodes := G.nodeOf_mem hx
  have hnn : 0 ≤ pieceNode G w T := G.nodeOf_nonneg _
  have hle : (pieceNode G w T : ℝ) ≤ ∑ i ∈ T, w i := G.nodeOf_le hx
  have hact0 : 0 ≤ ∑ j ∈ pieceBlock G w mesh T, w j := Finset.sum_nonneg (fun i _ => hw i)
  have hκ' : (G.κ : ℝ) ≥ 2 * mesh := hκ
  -- the two cases of the window
  have hzw : (pieceNode G w T = 0 ∧ pieceBlock G w mesh T = ∅) ∨
      (0 < pieceNode G w T ∧ (pieceNode G w T : ℝ) - 2 * mesh ≤ ∑ j ∈ pieceBlock G w mesh T, w j ∧
        ∑ j ∈ pieceBlock G w mesh T, w j ≤ (pieceNode G w T : ℝ) - mesh) := by
    by_cases h0 : pieceNode G w T = 0
    · left
      refine ⟨h0, ?_⟩
      unfold pieceBlock
      apply windowBlock_of_nonpos
      rw [h0]
      simp
    · right
      have hpos : 0 < pieceNode G w T := lt_of_le_of_ne hnn (Ne.symm h0)
      have hposR : (0 : ℝ) < pieceNode G w T := by exact_mod_cast hpos
      have h2 := G.two_mesh_le_node hmem h0 hg hd
      have hw' := windowBlock_spec T w hm (fun i _ => hw i) (fun i _ => hwm i) hposR h2
        (by linarith)
      exact ⟨hpos, hw'.1, hw'.2⟩
  refine ⟨hmem, hnn, G.nodeOf_le_top hx, G.theta_nonneg _, G.theta_le hnn,
    pieceBlock_subset G w mesh T, hact0, ?_, ?_, ?_, hle, ?_, ?_⟩
  · -- θ ≤ δ_act
    rcases hzw with ⟨h0, hJ⟩ | ⟨_, hlo, _⟩
    · rw [h0, G.theta_zero]
      simpa using hact0
    · have h1 : (pieceNode G w T : ℝ) - G.κ ≤ ∑ j ∈ pieceBlock G w mesh T, w j := by linarith
      have h2 : ((G.theta (pieceNode G w T) : ℚ) : ℝ) =
          max 0 ((pieceNode G w T : ℝ) - G.κ) := by
        unfold NodeGrid.theta
        push_cast
        rfl
      rw [h2]
      exact max_le hact0 h1
  · -- δ_act ≤ δ
    rcases hzw with ⟨h0, hJ⟩ | ⟨_, _, hhi⟩
    · rw [hJ, h0]
      simp
    · linarith
  · -- shift
    rcases hzw with ⟨h0, hJ⟩ | ⟨_, hlo, _⟩
    · rw [hJ, h0]
      simp
      linarith
    · linarith
  · rcases hzw with h | ⟨hpos, _, hhi⟩
    · exact Or.inl h
    · exact Or.inr ⟨hpos, hhi⟩
  · by_cases htop : (G.d : ℝ) ≤ ∑ i ∈ T, w i
    · exact Or.inl (G.nodeOf_top htop)
    · exact Or.inr ⟨not_le.mp htop, G.lt_nodeOf_add hx (not_le.mp htop)⟩

/-- **Frozen obligation of a piece.** A piece with frozen width `f`, transferable slots `T`,
non-transferable live width `X` (zero when every live slot is transferable) and total width
`f + X + Σ_T w ≥ b − δw`, at a non-top node, has `(b − θ) − ε − X ≤ f`. -/
theorem piece_frozen_obligation (G : NodeGrid) (w : α → ℝ) (T : Finset α) (hw : ∀ i, 0 ≤ w i)
    {f X b δw ε : ℝ} (hlow : pieceNode G w T ≠ G.d)
    (hsum : b - δw ≤ f + X + ∑ i ∈ T, w i) (hε : δw + G.g + G.κ ≤ ε) :
    b - (G.theta (pieceNode G w T) : ℝ) - ε - X ≤ f := by
  have hx : 0 ≤ ∑ i ∈ T, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hlt : (∑ i ∈ T, w i) < G.d := by
    by_contra h
    exact hlow (G.nodeOf_top (not_lt.mp h))
  have h := G.frozen_obligation (f := f + X) (b := b) (δw := δw) hx hlt (by linarith) hε
  unfold pieceNode
  linarith

end Piece

end
end QRH.MixedStep.Downstream

#print axioms QRH.MixedStep.Downstream.pieceFacts
#print axioms QRH.MixedStep.Downstream.piece_frozen_obligation
#print axioms QRH.MixedStep.Downstream.NodeGrid.top_slack
#print axioms QRH.MixedStep.Downstream.NodeGrid.frozen_obligation
