/- Copyright (c) 2026 Sil. Apache-2.0.
Scalar data and gates of one generic cube-free common-divisor step
G(B₀,L₀,c₀) → G(B,L,c) (CF §6–7, DS §4–5), and the native instance.

`SideGeometry` is the scalar geometry of one first-common side after selection
(CF §6): original marked width `S`, frozen marked width `f`, extracted common norm
width `cg ≥ f`, side ordinary width `PC` (the root ordinary width is `PC + cg - f`),
selected width `u`, retained marked width `s`, and the frequency defect `t = K₀ - K`.
The packed envelope is `H = 1 + t - 6u` (CF (6.1)) and the live width is `w = S - f`.

`StepGates.ledger` is CF (6.2)–(6.3): the leaf price at the side is paid by the selected
width, `price ≤ u + ε/16`, for every live width above the small-branch floor.
`StepGates.reference` collects the fixed root-reference/diagonal reserves of CF §7 and
DS §5 at `u_max = sel S` (the mesh is paid in `RootParameters`).

Deviations from the coordinator's design sketch (all forced by the mathematics):
* `face`: no `c ≤ c₀` — false for native steps (`face1 → face2` has `c = .067 > c₀ = .06`)
  and never used: the retained cap is the separate inequality `s ≤ c₀ H`. Added `c < 1/6`.
* `crossing`: the inheritance condition is `(L₀-L) s₀ ≤ B₀ - B` (the sketch had the
  reverse inequality). Roots with `S < s₀` satisfy `P + L₀ S ≤ B + (L₀-L) s₀ ≤ B₀`.
  `s₀ ≤ c₀` is only needed when that branch is nonempty, i.e. when `0 < s₀`; natively
  `s₀ = 0` and `c₀ > 0` is not a consequence of `NativeGates` when `a ≥ 1`.
* `SideGeometry.hS` is closed (`s₀ ≤ S`), so the native step (`s₀ = 0`) covers `S = 0`
  and the density step covers `v = 0`, where `HybridGates` is certified.
* `sel_spec` is stated on `[0,c]` (`sel ≤ w` is false for `w < 0`).
* the ledger no longer asserts `sel w + mesh ≤ w`: greedy selection only needs `sel w ≤ w`
  (in `sel_spec`), and the conjunct fails natively when `a ≥ 1`.
* `smallH` is replaced by `envelope.Hmin < 1` and the lemma `StepGates.small_envelope`;
  the small branch (`w < floor`, `u = 0`, native price) does not use `D.sel`, so it does
  not fit `SideGeometry D`.
* native selection fraction is `min a 1`: `NativeGates` allows `a ≥ 1` (large `L`), where
  one selects the whole live block, `s = 0` and the parent price vanishes. -/
import Submissions.sil_density_split_20261026.CubeFree.Price
import Submissions.sil_density_split_20261026.Source.NativeBootstrap
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false
namespace QRH.SilDensitySplit.CubeFree
noncomputable section

/-- Scalar data of a generic cube-free step. `sel ε w` is the target selected width at
live width `w`; `s₀` the crossing width below which roots are inherited. -/
structure StepData where
  B₀ : ℝ
  L₀ : ℝ
  c₀ : ℝ
  B : ℝ
  L : ℝ
  c : ℝ
  κ : ℝ
  s₀ : ℝ
  Hmin : ℝ
  Hmax : ℝ
  sel : ℝ → ℝ → ℝ
  price : Price

/-- Scalar geometry of one first-common side (CF §6). -/
structure SideGeometry (D : StepData) (ε mesh tl : ℝ) where
  S : ℝ
  f : ℝ
  cg : ℝ
  PC : ℝ
  u : ℝ
  s : ℝ
  t : ℝ
  hS : D.s₀ ≤ S ∧ S ≤ D.c
  hf : 0 ≤ f ∧ f ≤ cg
  hPC : 0 ≤ PC
  /-- the child root face, with root ordinary width `PC + (cg - f)`, up to the same
  `o(1)` tolerance `tl` as the frequency defect (subunit plain lengths, `ℓ(X) ≠ log_Z X`) -/
  hroot : PC + (cg - f) + D.L*S ≤ D.B + tl
  /-- greedy selection: one upward mesh error -/
  hsel : D.sel ε (S - f) ≤ u ∧ u ≤ D.sel ε (S - f) + mesh
  hs : 0 ≤ s ∧ s ≤ S - f - u
  /-- `K ≥ K₀ - o(1)`; `H ≤ 2 + o(1)` from `V_C ∣ C²`, `A ≤ 1` -/
  ht : -tl ≤ t ∧ t ≤ 1 + 6*u + tl

namespace SideGeometry
variable {D : StepData} {ε mesh tl : ℝ}
/-- Live marked width. -/
def w (g : SideGeometry D ε mesh tl) : ℝ := g.S - g.f
/-- Packed envelope `H = 2a - k + q_C = 1 + t - 6u` (CF (6.1)). -/
def H (g : SideGeometry D ε mesh tl) : ℝ := 1 + g.t - 6*g.u
end SideGeometry

/-- The ledger at a fixed loss `ε` with chosen floor, mesh and frequency tolerances. -/
def LedgerAt (D : StepData) (ε floor meshL tlL : ℝ) : Prop :=
  0 < floor ∧ floor ≤ ε/(16*D.κ) ∧ 0 < meshL ∧ 0 < tlL ∧
  ∀ mesh, 0 ≤ mesh → mesh ≤ meshL → ∀ tl, 0 ≤ tl → tl ≤ tlL →
  ∀ g : SideGeometry D ε mesh tl, floor ≤ g.w →
    D.Hmin ≤ g.H ∧ g.H ≤ D.Hmax ∧ D.price.f g.w g.PC g.s g.H ≤ g.u + ε/16

/-- The fixed root-reference and second-diagonal reserves (CF (7.1)–(7.2), DS §5),
at `u_max = sel S`. -/
def ReferenceAt (D : StepData) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ ε > 0, ∀ S, D.s₀ ≤ S → S ≤ D.c →
    ρ ≤ (1-D.B) + (D.L-2)*S - 9/2*D.sel ε S ∧
    ρ ≤ 1/20 + 3/2*(1-D.B) + (3/2*D.L-5/2)*S - 9/2*D.sel ε S ∧
    ρ ≤ (1-D.B) + (D.L-1)*S - 4*D.sel ε S ∧
    ρ ≤ 1/3 - 2*S - 3*D.sel ε S

/-- The scalar gates of a generic cube-free step. -/
structure StepGates (D : StepData) : Prop where
  face : D.B ≤ D.B₀ ∧ D.B₀ < 1 ∧ D.L < D.L₀ ∧ 1 < D.L ∧ 0 < D.c ∧ D.c < 1/6 ∧ D.c₀ < 1/6
  kappa : D.κ = 3/4
  crossing : 0 ≤ D.s₀ ∧ (D.L₀ - D.L)*D.s₀ ≤ D.B₀ - D.B ∧ (0 < D.s₀ → D.s₀ ≤ D.c₀)
  envelope : 0 < D.Hmin ∧ D.Hmin < 1 ∧ 3 ≤ D.Hmax
  sel_spec : ∀ ε > 0, MonotoneOn (D.sel ε) (Set.Icc 0 D.c) ∧
    ∀ w, 0 ≤ w → w ≤ D.c → 0 ≤ D.sel ε w ∧ D.sel ε w ≤ w
  ledger : ∀ ε > 0, ∃ p : ℝ × ℝ × ℝ, LedgerAt D ε p.1 p.2.1 p.2.2
  reference : ∃ ρ, ReferenceAt D ρ

namespace StepGates
variable {D : StepData}

/-- Chosen ledger parameters `(floor, meshL, tlL)` at loss `ε`. -/
def ledgerParams (G : StepGates D) (ε : ℝ) : ℝ × ℝ × ℝ :=
  if h : 0 < ε then Classical.choose (G.ledger ε h) else (1, 1, 1)

/-- The small-branch floor. -/
def floor (G : StepGates D) (ε : ℝ) : ℝ := (G.ledgerParams ε).1
/-- The largest mesh admitted by the ledger. -/
def meshL (G : StepGates D) (ε : ℝ) : ℝ := (G.ledgerParams ε).2.1
/-- The largest frequency tolerance admitted by the ledger. -/
def tlL (G : StepGates D) (ε : ℝ) : ℝ := (G.ledgerParams ε).2.2

theorem ledger_spec (G : StepGates D) {ε : ℝ} (hε : 0 < ε) :
    LedgerAt D ε (G.floor ε) (G.meshL ε) (G.tlL ε) := by
  have h := Classical.choose_spec (G.ledger ε hε)
  have e : G.ledgerParams ε = Classical.choose (G.ledger ε hε) := by
    unfold ledgerParams; simp [hε]
  simp only [floor, meshL, tlL, e]
  exact h

/-- The chosen reference reserve. -/
def refReserve (G : StepGates D) : ℝ := Classical.choose G.reference

theorem reference_spec (G : StepGates D) : ReferenceAt D G.refReserve :=
  Classical.choose_spec G.reference

/-- The small branch (`u = 0`, native price, CF §6 last paragraph): the envelope
`H = 1 + t` lies in `[Hmin, Hmax]` once `tl ≤ 1 - Hmin`. -/
theorem small_envelope (G : StepGates D) {t tl : ℝ} (htl : tl ≤ 1 - D.Hmin)
    (ht : -tl ≤ t ∧ t ≤ 1 + tl) :
    D.Hmin ≤ 1 + t ∧ 1 + t ≤ D.Hmax := by
  have := G.envelope
  constructor <;> linarith [ht.1, ht.2]

/-- Small-branch native price: below the floor the native cost is at most `ε/16`. -/
theorem small_price (G : StepGates D) {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ G.floor ε) :
    (3/4:ℝ) * max 0 s ≤ ε/16 := by
  obtain ⟨hf0, hf, -⟩ := G.ledger_spec hε
  rw [G.kappa] at hf
  have : max 0 s ≤ ε/12 := max_le (by positivity) (by linarith)
  linarith

/-- Inheritance below the crossing: a root of the child face with `S < s₀` lies in
the parent face. -/
theorem inherit (G : StepGates D) {P S : ℝ} (hS0 : 0 ≤ S) (hS : S < D.s₀)
    (hroot : P + D.L*S ≤ D.B) : P + D.L₀*S ≤ D.B₀ ∧ S ≤ D.c₀ := by
  obtain ⟨-, -, hL, -⟩ := G.face
  obtain ⟨-, hcr, hc⟩ := G.crossing
  refine ⟨?_, hS.le.trans (hc (hS0.trans_lt hS))⟩
  have : (D.L₀ - D.L)*S ≤ (D.L₀ - D.L)*D.s₀ :=
    mul_le_mul_of_nonneg_left hS.le (by linarith)
  nlinarith

end StepGates

/-! ### The native instance -/

theorem _root_.QRH.SilDensitySplit.NativeGates.L₀_pos {p n : Face} {a : ℝ} (h : NativeGates p n a) : 0 < p.L := by
  have := h.principal; have := h.L_lt; have := h.a_pos; linarith

/-- Effective native selection fraction `min a 1`. -/
def nativeFrac (a : ℝ) : ℝ := min a 1

/-- Native step data: parent price, selection `min a 1 · w`, `s₀ = 0`. -/
def nativeData (p n : Face) (a : ℝ) (h : NativeGates p n a) : StepData where
  B₀ := p.B
  L₀ := p.L
  c₀ := p.c
  B := n.B
  L := n.L
  c := n.c
  κ := 3/4
  s₀ := 0
  Hmin := (1 - 6*nativeFrac a*n.c)/2
  Hmax := 3
  sel := fun _ w => nativeFrac a * w
  price := parentPrice (3/4) p.B p.L p.c (by norm_num) h.L₀_pos

section native
variable {p n : Face} {a : ℝ}

theorem nativeFrac_pos (h : NativeGates p n a) : 0 < nativeFrac a :=
  lt_min h.a_pos one_pos

theorem nativeFrac_le_one (a : ℝ) : nativeFrac a ≤ 1 := min_le_right _ _

theorem nativeFrac_le (a : ℝ) : nativeFrac a ≤ a := min_le_left _ _

theorem nativeFrac_of_lt {a : ℝ} (ha : a < 1) : nativeFrac a = a := min_eq_left ha.le

theorem _root_.QRH.SilDensitySplit.NativeGates.c_lt (h : NativeGates p n a) : n.c < 1/6 := by
  have := h.refPos; have := h.cap_pos; have := h.a_pos; nlinarith

theorem _root_.QRH.SilDensitySplit.NativeGates.H_eff (h : NativeGates p n a) : 0 < 1 - 6*nativeFrac a*n.c := by
  rcases lt_or_ge a 1 with ha | ha
  · rw [nativeFrac_of_lt ha]; exact h.H
  · have : nativeFrac a = 1 := min_eq_right ha
    rw [this]; have := h.c_lt; linarith

/-- Retained native cap (CF §1): `s - c₀ H ≤ 0`, linear in `w ∈ [0,c]`. -/
theorem native_cap_aux {a c c₀ w u s t tl mesh : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc₀ : 0 < c₀) (hw : w ≤ c) (hu0 : a*w ≤ u) (hu1 : u ≤ a*w + mesh) (hs : s ≤ w - u)
    (ht : -tl ≤ t) (hsmall : c₀*(tl + 6*mesh) ≤ c₀*(1-6*a*c) - (1-a)*c) :
    s - c₀*(1 + t - 6*u) ≤ 0 := by
  have hcoef : 0 ≤ (1-a) + 6*a*c₀ := by have := mul_pos ha0 hc₀; linarith
  linarith [mul_nonneg hc₀.le (show 0 ≤ t + tl by linarith),
    mul_nonneg hc₀.le (show 0 ≤ a*w + mesh - u by linarith),
    mul_nonneg hcoef (show 0 ≤ c - w by linarith)]

/-- The face defect at the side (CF (6.2), DS §4 `F`), natively without the crossing. -/
theorem native_defect_aux {B B₀ L L₀ PC cg f S w u s t tl : ℝ} (hB : B ≤ B₀) (hB₀ : 0 ≤ B₀)
    (hL : 0 ≤ L) (hL₀ : 0 ≤ L₀) (hf : 0 ≤ f) (hfcg : f ≤ cg) (hw : w = S - f)
    (hroot : PC + (cg - f) + L*S ≤ B + tl) (hs : s ≤ w - u) (ht : -tl ≤ t) :
    PC + L₀*s - B₀*(1 + t - 6*u) ≤ (L₀ - L)*w + (6*B₀ - L₀)*u + (B₀*tl + tl) := by
  subst hw
  linarith [mul_nonneg hL hf, mul_le_mul_of_nonneg_left hs hL₀,
    mul_nonneg hB₀ (show 0 ≤ t + tl by linarith)]

/-- Retention and overshoot (CF (6.3)): with `u = a w + δ`,
`κ·defect/L₀ ≤ u - retention·w - overshoot·δ + κ B₀ tl/L₀ ≤ u + ε/16`. -/
theorem native_retention_aux {a B₀ L L₀ w u tl ε : ℝ} (hL₀ : 0 < L₀) (hB₀ : 0 ≤ B₀)
    (hB₁ : B₀ < 1) (hw : 0 ≤ w) (hu0 : a*w ≤ u) (htl : 0 ≤ tl) (htlε : tl ≤ L₀*ε/24)
    (hret : 0 < a - 3/4*(L₀ - L + (6*B₀ - L₀)*a)/L₀)
    (hov : 0 < 1 - 3/4*(6*B₀ - L₀)/L₀) :
    3/4*(((L₀ - L)*w + (6*B₀ - L₀)*u + (B₀*tl + tl))/L₀) ≤ u + ε/16 := by
  have e1 : 3/4*(((L₀ - L)*w + (6*B₀ - L₀)*u + (B₀*tl + tl))/L₀) =
      u - (a - 3/4*(L₀ - L + (6*B₀ - L₀)*a)/L₀)*w
        - (1 - 3/4*(6*B₀ - L₀)/L₀)*(u - a*w) + 3/4*((B₀*tl + tl)/L₀) := by
    field_simp; ring
  rw [e1]
  have h1 := mul_nonneg hret.le hw
  have h2 := mul_nonneg hov.le (show 0 ≤ u - a*w by linarith)
  have h3 : (B₀*tl + tl)/L₀ ≤ ε/12 := by
    rw [div_le_iff₀ hL₀]
    linarith [mul_nonneg (show 0 ≤ 1 - B₀ by linarith) htl]
  linarith

/-- The native ledger (CF (6.2)–(6.3)). With `u = a w + δ`, `0 ≤ δ ≤ mesh`:
`κ·defect/L₀ - u ≤ -retention·w - overshoot·δ + κ B₀ tl/L₀`, and the retained cap
`s - c₀ H ≤ -(cap gate) + c₀ (tl + 6 mesh) ≤ 0`. If `a ≥ 1` the whole live block is
selected, `s = 0`, and the parent price vanishes. -/
theorem native_ledger (h : NativeGates p n a) {ε : ℝ} (hε : 0 < ε) :
    LedgerAt (nativeData p n a h) ε (ε/16)
      (min ((1 - 6*nativeFrac a*n.c)/24) ((p.c*(1 - 6*a*n.c) - (1-a)*n.c)/2))
      (min (min ((1 - 6*nativeFrac a*n.c)/4) 1)
        (min (3*(p.c*(1 - 6*a*n.c) - (1-a)*n.c)) (min (p.L*ε/24) (ε/32)))) := by
  have hh0 : 0 < 1 - 6*nativeFrac a*n.c := h.H_eff
  have hcap : 0 < p.c*(1 - 6*a*n.c) - (1-a)*n.c := h.cap
  have hL₀ := h.L₀_pos
  refine ⟨by positivity, ?_, lt_min (by positivity) (by positivity),
    lt_min (lt_min (by positivity) one_pos) (lt_min (by positivity) (by positivity)), ?_⟩
  · show ε/16 ≤ ε/(16*(3/4))
    apply div_le_div_of_nonneg_left hε.le (by norm_num) (by norm_num)
  intro mesh hmesh hmeshL tl htl htlL g hfloor
  have hm1 : mesh ≤ (1 - 6*nativeFrac a*n.c)/24 := hmeshL.trans (min_le_left _ _)
  have hm2 : mesh ≤ (p.c*(1 - 6*a*n.c) - (1-a)*n.c)/2 := hmeshL.trans (min_le_right _ _)
  have ht1 : tl ≤ (1 - 6*nativeFrac a*n.c)/4 :=
    htlL.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ht2 : tl ≤ 1 := htlL.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht3 : tl ≤ 3*(p.c*(1 - 6*a*n.c) - (1-a)*n.c) :=
    htlL.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht4 : tl ≤ p.L*ε/24 :=
    htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht5 : tl ≤ ε/32 :=
    htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hS := g.hS
  have hf := g.hf
  have hPC := g.hPC
  have hroot := g.hroot
  have hsel := g.hsel
  have hs := g.hs
  have ht := g.ht
  simp only [nativeData] at hS hroot hsel
  have hw : g.w = g.S - g.f := rfl
  have hH : g.H = 1 + g.t - 6*g.u := rfl
  have hwpos : 0 < g.w := lt_of_lt_of_le (by positivity) hfloor
  have ha' := nativeFrac_pos h
  have ha1 := nativeFrac_le_one a
  have hc := h.cap_pos
  have hLn : 2 < n.L := by have := h.principal; have := h.a_pos; linarith
  have hu0 : nativeFrac a * g.w ≤ g.u := hsel.1
  have hu1 : g.u ≤ nativeFrac a * g.w + mesh := hsel.2
  have hwc : g.w ≤ n.c := by rw [hw]; linarith
  have huw : nativeFrac a * g.w ≤ nativeFrac a * n.c :=
    mul_le_mul_of_nonneg_left hwc ha'.le
  have hupos : 0 ≤ g.u := le_trans (mul_nonneg ha'.le hwpos.le) hu0
  refine ⟨?_, ?_, ?_⟩
  · show (1 - 6*nativeFrac a*n.c)/2 ≤ g.H
    rw [hH]; linarith
  · show g.H ≤ 3
    rw [hH]; linarith
  show 3/4 * deletionNeed p.B p.L p.c g.PC g.s g.H ≤ g.u + ε/16
  rcases le_or_gt g.s 0 with hsle | hspos
  · rw [deletionNeed_of_nonpos hsle]; linarith
  have ha : a < 1 := by
    by_contra hna
    have h1 : nativeFrac a = 1 := min_eq_right (not_lt.mp hna)
    rw [h1] at hu0
    have : g.s ≤ g.w - g.u := by rw [hw]; linarith
    linarith
  rw [nativeFrac_of_lt ha] at hu0 hu1
  have hBB := h.B_le
  have hB₁ := h.B_lt
  have hB₀ : 0 < p.B := by
    have hSf : ε/16 ≤ g.S := by rw [hw] at hfloor; linarith
    have : 2*(ε/16) ≤ n.L*g.S := mul_le_mul hLn.le hSf (by positivity) (by linarith)
    linarith
  have hc₀ : 0 < p.c := by
    have h1 : 0 < (1-a)*n.c := mul_pos (by linarith) hc
    have h2 : 0 < 1 - 6*a*n.c := h.H
    by_contra hneg
    have : p.c*(1 - 6*a*n.c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) h2.le
    linarith
  have hc₀6 := h.cap_lt
  have hcapH : g.s - p.c*g.H ≤ 0 := by
    rw [hH]
    refine native_cap_aux h.a_pos ha hc₀ hwc hu0 hu1 (by rw [hw]; linarith) ht.1 ?_
    linarith [mul_le_mul_of_nonneg_right hc₀6.le (show 0 ≤ tl + 6*mesh by positivity)]
  have hneed := deletionNeed_le_defect (B₀:=p.B) (L₀:=p.L) (P:=g.PC) hcapH
  have hdef : g.PC + p.L*g.s - p.B*g.H ≤
      (p.L - n.L)*g.w + (6*p.B - p.L)*g.u + (p.B*tl + tl) := by
    rw [hH]
    exact native_defect_aux hBB hB₀.le (by linarith) hL₀.le hf.1 hf.2 hw hroot
      (by rw [hw]; linarith) ht.1
  have hret := h.retention
  have hov := h.overshoot
  simp only [nativeK] at hret hov
  have hkey := native_retention_aux (L:=n.L) hL₀ hB₀.le hB₁ hwpos.le hu0 htl ht4 hret hov
  calc 3/4 * deletionNeed p.B p.L p.c g.PC g.s g.H
      ≤ 3/4 * max 0 ((g.PC + p.L*g.s - p.B*g.H)/p.L) :=
        mul_le_mul_of_nonneg_left hneed (by norm_num)
    _ ≤ 3/4 * max 0 (((p.L - n.L)*g.w + (6*p.B - p.L)*g.u + (p.B*tl + tl))/p.L) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact max_le_max le_rfl (div_le_div_of_nonneg_right hdef hL₀.le)
    _ ≤ g.u + ε/16 := by
        rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/4)]
        refine max_le (by linarith) hkey

/-- The native reference reserves (`principal`, `secondRef`, `diagonal`, `refPos`). -/
theorem native_reference (h : NativeGates p n a) :
    ReferenceAt (nativeData p n a h) (min (1 - n.B) (1/3 - (2 + 3*a)*n.c)) := by
  have hB : n.B < 1 := lt_of_le_of_lt h.B_le h.B_lt
  have hr := h.refPos
  have hpr := h.principal
  have hsr := h.secondRef
  have hdg := h.diagonal
  have ha' := nativeFrac_pos h
  have haa := nativeFrac_le a
  have hc := h.cap_pos
  refine ⟨lt_min (by linarith) (by linarith), ?_⟩
  intro ε _ S hS0 hSc
  simp only [nativeData] at hS0 hSc ⊢
  have hm1 : min (1 - n.B) (1/3 - (2 + 3*a)*n.c) ≤ 1 - n.B := min_le_left _ _
  have hm2 : min (1 - n.B) (1/3 - (2 + 3*a)*n.c) ≤ 1/3 - (2 + 3*a)*n.c := min_le_right _ _
  have e1 : 0 ≤ (n.L - 2 - 9/2*nativeFrac a)*S := mul_nonneg (by linarith) hS0
  have e2 : 0 ≤ (3/2*n.L - 5/2 - 9/2*nativeFrac a)*S := mul_nonneg (by linarith) hS0
  have e3 : 0 ≤ (n.L - 1 - 4*nativeFrac a)*S := mul_nonneg (by linarith) hS0
  have e4 : (2 + 3*nativeFrac a)*S ≤ (2 + 3*a)*n.c :=
    mul_le_mul (by linarith) hSc hS0 (by linarith)
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The native scalar chain certificate implies the generic step gates. -/
theorem stepGates_of_native (h : NativeGates p n a) : StepGates (nativeData p n a h) where
  face := by
    have := h.principal; have := h.a_pos
    exact ⟨h.B_le, h.B_lt, h.L_lt, show 1 < n.L by linarith, h.cap_pos, h.c_lt, h.cap_lt⟩
  kappa := rfl
  crossing := by
    refine ⟨le_rfl, ?_, fun h0 => absurd h0 (lt_irrefl 0)⟩
    show (p.L - n.L)*0 ≤ p.B - n.B
    have := h.B_le; simp; linarith
  envelope := by
    have := h.H_eff
    refine ⟨by show 0 < (1 - 6*nativeFrac a*n.c)/2; positivity, ?_, by norm_num [nativeData]⟩
    show (1 - 6*nativeFrac a*n.c)/2 < 1
    have := nativeFrac_pos h; have := h.cap_pos; nlinarith
  sel_spec := by
    intro ε _
    have ha' := nativeFrac_pos h
    have ha1 := nativeFrac_le_one a
    refine ⟨fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy ha'.le, fun w hw _ => ?_⟩
    exact ⟨mul_nonneg ha'.le hw, show nativeFrac a * w ≤ w by nlinarith⟩
  ledger := fun ε hε => ⟨(_, _, _), native_ledger h hε⟩
  reference := ⟨_, native_reference h⟩

end native

end
end QRH.SilDensitySplit.CubeFree
