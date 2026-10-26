/- Mixed step (L4/L5, F5/N6): new in this submission; uses Collet's definitions (`Initial`,
`InitialGeometry`, `globalFace`) and the ledger's `vnode2` by import.

Glue for `regular_supplier3` (`Downstream/Contract3.lean`, `RegularSupplier3Statement`):
* `uniform_regular_constants`: finitely many suppliers of the regular shape (degree, controls,
  `C`, `τ`, `σ`, monotone in each) have one common set of constants. It is used over the nodes of the
  grid and over the blocks `J`.
* `restrict_face_vnode2`, `restrict_initialGeometry`: the residual `Initial'.restrict i J` of the
  original initial datum satisfies Collet's `InitialGeometry` at the virtual node
  `vnode2 n low b δ θ`, at the width `b − θ` and with cell width `width + κ`, when
  `θ ≤ Σ_J w ≤ δ ≤ θ + κ`. -/
import Submissions.arvi_mixed_step.Downstream.Contract3
import Submissions.arvi_mixed_step.Downstream.RestrictCanonical
import Submissions.arvi_mixed_step.Downstream.MainRestrict
import Submissions.arvi_mixed_step.Downstream.Pieces
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularLowPointData

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.MixedStep.Downstream
noncomputable section
open OAI OAI.SevenEighths
local notation "O" => HeckeFamily.O
open QRH.Record1252270103Source QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
open Record1252270103Finite QRH.MixedStep.Ledger QRH.Record12518109Source
open CenteredMomentEnergyBands CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile QRH.MixedStep.Residual
open QRH.Record1252270103Graph Cycle61InitialMass CenteredMomentEnergyBandMonotonicity Filter
open CenteredMomentFiniteProfileExceptional
open scoped BigOperators

/-! ### Common constants for finitely many suppliers -/

/-- **Finitely many suppliers have common constants.** The predicate is monotone in the degree, the
control set and `C`, and antitone in `τ` and `σ` (as long as they stay positive). -/
theorem uniform_regular_constants {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (B : ι → ℕ → Finset (ℕ×ℕ) → ℝ → ℝ → ℝ → Prop)
    (hmono : ∀ i (d d' : ℕ) (Sc Sc' : Finset (ℕ×ℕ)) (C C' τ τ' σ σ' : ℝ), d ≤ d' → Sc ⊆ Sc' →
      C ≤ C' → τ' ≤ τ → σ' ≤ σ → 0 < τ' → 0 < σ' → B i d Sc C τ σ → B i d' Sc' C' τ' σ')
    (h : ∀ i ∈ S, ∃ d : ℕ, ∃ Sc : Finset (ℕ×ℕ), (0,0) ∈ Sc ∧
      ∃ C τ σ : ℝ, 0 < C ∧ 0 < τ ∧ 0 < σ ∧ B i d Sc C τ σ) :
    ∃ d : ℕ, ∃ Sc : Finset (ℕ×ℕ), (0,0) ∈ Sc ∧
      ∃ C τ σ : ℝ, 0 < C ∧ 0 < τ ∧ 0 < σ ∧ ∀ i ∈ S, B i d Sc C τ σ := by
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, {(0,0)}, Finset.mem_singleton_self _, 1, 1, 1, one_pos, one_pos, one_pos,
        fun i hi => by simp at hi⟩
  | insert j S hj ih =>
      obtain ⟨d₁, S₁, h₁, C₁, τ₁, σ₁, hC₁, hτ₁, hσ₁, hB₁⟩ := h j (Finset.mem_insert_self _ _)
      obtain ⟨d₂, S₂, _, C₂, τ₂, σ₂, _, hτ₂, hσ₂, hB₂⟩ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine ⟨max d₁ d₂, S₁ ∪ S₂, Finset.mem_union_left _ h₁, max C₁ C₂, min τ₁ τ₂, min σ₁ σ₂,
        lt_max_of_lt_left hC₁, lt_min hτ₁ hτ₂, lt_min hσ₁ hσ₂, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hmono _ _ _ _ _ _ _ _ _ _ _ (le_max_left _ _) Finset.subset_union_left
          (le_max_left _ _) (min_le_left _ _) (min_le_left _ _) (lt_min hτ₁ hτ₂) (lt_min hσ₁ hσ₂) hB₁
      · exact hmono _ _ _ _ _ _ _ _ _ _ _ (le_max_right _ _) Finset.subset_union_right
          (le_max_right _ _) (min_le_right _ _) (min_le_right _ _) (lt_min hτ₁ hτ₂) (lt_min hσ₁ hσ₂)
          (hB₂ i hi)

/-- Products of five nonnegative factors are monotone in four of them. -/
theorem mono_five {a a' b b' g c c' e e' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (hb : 0 ≤ b) (hbb : b ≤ b')
    (hg : 0 ≤ g) (hc : 0 ≤ c) (hcc : c ≤ c') (he : 0 ≤ e) (hee : e ≤ e') :
    a*b*g*c*e ≤ a'*b'*g*c'*e' := by
  have h1 : a*b ≤ a'*b' := mul_le_mul haa hbb hb (ha.trans haa)
  have h2 : a*b*g ≤ a'*b'*g := mul_le_mul_of_nonneg_right h1 hg
  have h0 : 0 ≤ a'*b'*g := mul_nonneg (mul_nonneg (ha.trans haa) (hb.trans hbb)) hg
  have h3 : a*b*g*c ≤ a'*b'*g*c' := mul_le_mul h2 hcc hc h0
  exact mul_le_mul h3 hee he (mul_nonneg h0 (hc.trans hcc))

/-- **Uniform constants over the nodes and blocks.** -/
theorem regular_supplier3_of_at (K:ℚ)(n low:Source)(b:ℚ)(mesh ξ reserve width:ℝ)(G:NodeGrid)
    (φ:ℚ→ℝ)(h:∀δ∈G.nodes,RegularJointSupplier3At K n low b mesh ξ reserve width G φ δ) :
    RegularJointSupplier3 K n low b mesh ξ reserve width G φ := by
  intro α _ _ rayM _ H hH Wslot hW hsW bΦ hbΦ η η₀ Q hQM hQ hQt hQ72 R₀ hR₀
  let S : Finset (ℚ × Finset α) := G.nodes ×ˢ Finset.univ
  have hper := fun (x : ℚ × Finset α) (hx : x ∈ S) =>
    h x.1 (Finset.mem_product.mp hx).1 α rayM H hH Wslot hW hsW bΦ hbΦ η η₀ Q hQM hQ hQt hQ72 R₀ hR₀ x.2
  choose! d Sc h00 C τ σ hC hτ hσ hev using hper
  have hx0 : (G.d, (∅ : Finset α)) ∈ S :=
    Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩
  have hSne : S.Nonempty := ⟨_, hx0⟩
  refine ⟨S.sup d, insert ((0:ℕ),(0:ℕ)) (S.biUnion Sc), Finset.mem_insert_self _ _,
    1 + ∑ x ∈ S, C x, S.inf' hSne τ, S.inf' hSne σ,
    by have := Finset.sum_nonneg (fun x hx => (hC x hx).le); linarith,
    (Finset.lt_inf'_iff hSne).2 (fun x hx => hτ x hx),
    (Finset.lt_inf'_iff hSne).2 (fun x hx => hσ x hx), ?_⟩
  filter_upwards [(Filter.eventually_all_finset S).2 hev] with Z hZ
  refine ⟨(hZ _ hx0).1, ?_⟩
  intro hZ' θ w v t ht height hw hwm hh hv hext p X₁ X₂ hX₁ hX₂ hadm hcross hwlo hwhi Y₂ hy₂ hyl hyr
    Y₁ hY₂ hY₁ hprod s modifier W N amp P δ hδ J hθJ hJδ hsh sv Label instL reflected bin column hLive
    seed hseed hdvd hinj common scalar H0 labels radius alloc hJ hfroz hφ ray χ₀
    extra amplitude chars Hv Tsecv f
  have hx : (δ, J) ∈ S := Finset.mem_product.mpr ⟨hδ, Finset.mem_univ _⟩
  have hZ1 : 1 ≤ Z := hZ'.le
  have hext' : 1+|t|+|ht|+height ≤ Z^(τ (δ, J)) :=
    hext.trans (Real.rpow_le_rpow_of_exponent_le hZ1 (Finset.inf'_le _ hx))
  have hb := (hZ (δ, J) hx).2 hZ' θ w v t ht height hw hwm hh hv hext' p X₁ X₂ hX₁ hX₂ hadm hcross
    hwlo hwhi hy₂ hyl hyr hθJ hJδ hsh reflected bin column hLive seed hseed hdvd hinj alloc hJ hfroz hφ
    ray χ₀
  refine hb.trans ?_
  have hbase : 1 ≤ 1+|ht|+height := by have := abs_nonneg ht; linarith
  have hCle : C (δ, J) ≤ 1 + ∑ x ∈ S, C x := by
    have := Finset.single_le_sum (fun y hy => (hC y hy).le) hx
    linarith
  have hSc : Sc (δ, J) ⊆ insert ((0:ℕ),(0:ℕ)) (S.biUnion Sc) := fun z hz =>
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨(δ, J), hx, hz⟩)
  have hG : 0 ≤ geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin :=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  exact mono_five (hC _ hx).le hCle (sq_nonneg _)
    (pow_le_pow_left₀ (p.control_nonneg _) (profile_control_mono p hSc) 2) hG
    (pow_nonneg (zero_le_one.trans hbase) _) (pow_le_pow_right₀ hbase (Finset.le_sup hx))
    (Real.rpow_nonneg (zero_le_one.trans hZ1) _)
    (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith [Finset.inf'_le σ hx]))

/-! ### The residual at a virtual node -/

section Residual
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Removing a block of width at least `θ` moves a global-face cell into the face whose budget is
lowered by `L·θ` (the face of `vnode2 … θ`). -/
theorem restrict_face_vnode2 (B L cap θ m₁ m₂ : ℝ) (hL : 0 ≤ L) (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (J : Finset α) (hθJ : θ ≤ ∑ j ∈ J, w j)
    (h : (globalFace B L cap).Admissible m₁ m₂ (∑ i, w i) 1) :
    (globalFace (B - L*θ) L cap).Admissible m₁ m₂ (∑ i : {i // i ∉ J}, w i.val) 1 := by
  have hsum := restrict_width_sum w J
  have hres0 : 0 ≤ ∑ i : {i // i ∉ J}, w i.val := Finset.sum_nonneg (fun i _ => hw i.val)
  simp only [SourceFace.Admissible, globalFace, mul_one] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hLθ : L*θ ≤ L*∑ j ∈ J, w j := mul_le_mul_of_nonneg_left hθJ hL
  have hLres : 0 ≤ L*∑ i : {i // i ∉ J}, w i.val := mul_nonneg hL hres0
  have hLsum : L*(∑ i : {i // i ∉ J}, w i.val) + L*(∑ j ∈ J, w j) = L*∑ i, w i := by
    rw [← mul_add, hsum]
  refine ⟨h1, ?_, h3, ?_, hres0, ?_, ?_⟩
  · linarith
  · linarith
  · have hJ0 : 0 ≤ ∑ j ∈ J, w j := Finset.sum_nonneg (fun j _ => hw j)
    linarith
  · linarith

/-- **The residual initial datum at the virtual node.** -/
theorem restrict_initialGeometry {rayM : Ideal O} [NeZero rayM] {H : Subgroup (O ⧸ rayM)ˣ} {Z : ℝ}
    (i : Initial (α := α) rayM H Z) (n low : Source) (b δ θ : ℚ) (width mesh r κ : ℝ)
    (hw : ∀ j, 0 ≤ i.w j) (hwm : ∀ j, i.w j ≤ mesh)
    (hface : (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z i.X₁) (length Z i.X₂) (∑ j, i.w j) 1)
    (hlo : (b:ℝ) - width ≤ ∑ j, i.w j) (hhi : (∑ j, i.w j) ≤ b)
    (hr : 0 ≤ r) (hl1 : Z^r ≤ i.X₁) (hl2 : Z^r ≤ i.X₂) (href : i.Y₂ = Z^r)
    (hL : 0 ≤ (n.L:ℝ)) (J : Finset α) (hθJ : (θ:ℝ) ≤ ∑ j ∈ J, i.w j)
    (hJδ : ∑ j ∈ J, i.w j ≤ δ) (hκ : (δ:ℝ) - θ ≤ κ) :
    InitialGeometry (Initial'.restrict i J) (vnode2 n low b δ θ) ((b - θ : ℚ) : ℝ) (width + κ)
      mesh r := by
  have hsum := restrict_width_sum i.w J
  have hres : (∑ j : {j // j ∉ J}, (Initial'.restrict i J).w j) =
      ∑ j : {j // j ∉ J}, i.w j.val := rfl
  have hB : (((vnode2 n low b δ θ).B : ℚ) : ℝ) = (n.B:ℝ) - (n.L:ℝ)*(θ:ℝ) := by
    simp only [vnode2_B]; push_cast; ring
  have hLv : (((vnode2 n low b δ θ).L : ℚ) : ℝ) = (n.L:ℝ) := by simp only [vnode2_L]
  have hcv : (((vnode2 n low b δ θ).cap : ℚ) : ℝ) = (n.cap:ℝ) := by simp only [vnode2_cap]
  have hbθ : ((b - θ : ℚ) : ℝ) = (b:ℝ) - (θ:ℝ) := by push_cast; ring
  refine ⟨fun j => hw j.val, fun j => hwm j.val, ?_, ?_, ?_, hr, hl1, hl2, href⟩
  · rw [hB, hLv, hcv, hres]
    exact restrict_face_vnode2 (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) (θ:ℝ) _ _ hL i.w hw J hθJ hface
  · rw [hbθ, hres]
    linarith
  · rw [hbθ, hres]
    linarith

/-- The δ-shift of the residual at the node `δ`: the virtual amplitude of `vnode2 … δ θ` is `r + δ`,
the log-volume drop is `Σ_J w`, and `δ − Σ_J w ≤ 2·mesh`. -/
theorem residual_shift (n low : Source) (b δ θn : ℚ) (hden : sourceDen n low ≠ 0)
    (s : Input α) (J : Finset α) (w : α → ℝ) (Z mesh : ℝ) (hZ : 1 < Z) (hP : ∀ i, s.P i = Z^(w i))
    (hshift : (δ:ℝ) - ∑ j ∈ J, w j ≤ 2*mesh) :
    sourceAReal (vnode2 n low b δ θn) low ((b - θn : ℚ) : ℝ) - (n.lowFee:ℝ) ≤
      Real.logb Z (volume s) - Real.logb Z (volume (s.restrict J)) + 2*mesh := by
  rw [(vnode2_real n low b δ θn hden).2.1, restrict_logb_volume s w hZ hP J]
  linarith

/-- The frozen width of a label is unchanged by the restriction (`residual_frozen_width`), so a
frozen margin on the original widths is one on the residual widths. -/
theorem frozen_margin_restrict (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) (w : α → ℝ) (φ : ℝ)
    (hφ : φ ≤ (∑ i, w i) - ∑ i ∈ liveIndices B.val, w i) :
    φ ≤ (∑ i : {i // i ∉ J}, w i.val) - ∑ i ∈ liveIndices (allocRestrict s C B J hJ).val, w i.val := by
  rw [residual_frozen_width s C B J hJ w]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => B.val (Sum.inl i) = 1) w
  have hlive : liveIndices B.val = Finset.univ.filter (fun i => B.val (Sum.inl i) = 1) := rfl
  rw [hlive] at hφ
  linarith

/-- The node facts of `Scalar_mx` at `vnode2 n low b δ θn` (width `b − θn`), from the grid-level
budgets: the loss is the HIGH budget `θ`, the residual cell width is `width + κ`. -/
theorem scalar_vnode2 (n low : Source) (b δ θn : ℚ) (reserve θ mesh ξ width κ : ℝ)
    (hgeom : QRH.MixedStep.Downstream.NodeGeometry_mx (vnode2 n low b δ θn) low ((b - θn : ℚ) : ℝ))
    (hlow : ParentGood low) (ha : 0 < (n.allowance:ℝ))
    (hf : QRH.Record1252270103Source.PhysicalAnalytic.FixedBudget reserve 100 100 1 θ)
    (hr : reserve ≤ (n.allowance:ℝ)) (hθstep : θ ≤ PhysicalLowGuard.step n)
    (hξ : 0 < ξ) (hξθ : ξ ≤ θ) (hm : 0 ≤ mesh) (hmesh : 100*mesh ≤ θ)
    (hwidth0 : 0 ≤ width) (hκ0 : 0 ≤ κ) (hwidth : width + κ ≤ θ) :
    Scalar_mx (vnode2 n low b δ θn) low ((b - θn : ℚ) : ℝ) θ mesh ξ (width + κ) := by
  have hθ := hf.positive
  have htiny := hf.tiny
  have hθsmall : θ ≤ (n.allowance:ℝ)/16 := by linarith
  have hstep : PhysicalLowGuard.step (vnode2 n low b δ θn) = PhysicalLowGuard.step n := rfl
  have hall : ((vnode2 n low b δ θn).allowance:ℝ) = (n.allowance:ℝ) := rfl
  exact ⟨hgeom, hlow, hall ▸ ha, hθ, hall ▸ hθsmall, hstep ▸ hθstep, hξ, hξθ, hm,
    by rw [hall]; linarith, by linarith, hstep ▸ (hwidth.trans hθstep)⟩

end Residual

end
end QRH.MixedStep.Downstream
#print axioms QRH.MixedStep.Downstream.uniform_regular_constants
#print axioms QRH.MixedStep.Downstream.regular_supplier3_of_at
#print axioms QRH.MixedStep.Downstream.restrict_initialGeometry
#print axioms QRH.MixedStep.Downstream.residual_shift
#print axioms QRH.MixedStep.Downstream.frozen_margin_restrict
#print axioms QRH.MixedStep.Downstream.scalar_vnode2
