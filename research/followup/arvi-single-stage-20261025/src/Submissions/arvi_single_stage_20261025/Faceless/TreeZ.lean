import Submissions.arvi_single_stage_20261025.Faceless.Packed

/-!
# Fast HIGH trees: the interval tests read the packed leaf polynomials directly

`IPoly.uCheckI` unpacks every leaf polynomial to a list of integers and re-packs it for every
`y`-interval. Here the interval test works on the packed numbers. If `r` packs `A − B` at base `X`
(`r.pos = A(X)`) and `k + 1 ≤ 2^e`, the scaled shift `t ↦ 2^{e(L−1)} A((k + t)/2^e)` has natural
coefficients, and its value at `Y = 2^e X − k` is `2^{e(L−1)} A(X)`. So its coefficients are the
base-`Y` digits of `2^{e(L−1)} r.pos`, exactly when their sum `2^{e(L−1)} A((k+1)/2^e)` is below
`Y`, which `2^{e(L−1)} r.pos1 < Y` guarantees. The test `tm1` then runs on these digits in
natural numbers. The base `X` is data, and the packed inputs are shared by all leaves of a tree.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless

namespace IPoly

/-- `Σ |a_i − b_i|`, in natural numbers. -/
def absDiffSum : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => (a - b) + (b - a) + absDiffSum as bs
  | _, _ => 0

/-- `tm1` of the coefficients `a_i − b_i`, in natural numbers. -/
def tm1D : List ℕ → List ℕ → Bool
  | [a₀], [b₀] => decide (b₀ < a₀)
  | a₀ :: a₁ :: as, b₀ :: b₁ :: bs =>
      let S := absDiffSum as bs
      decide (b₀ + S < a₀) && decide (b₀ + b₁ + S < a₀ + a₁)
  | _, _ => false

theorem absDiffSum_cast (A B : List ℕ) (h : A.length = B.length) :
    ((absDiffSum A B : ℕ) : ℤ) = absSum (List.zipWith (fun (a b : ℕ) => (a:ℤ) - (b:ℤ)) A B) := by
  induction A generalizing B with
  | nil => cases B <;> simp_all [absDiffSum, absSum]
  | cons a A ih =>
    cases B with
    | nil => simp at h
    | cons b B =>
      simp only [absDiffSum, List.zipWith_cons_cons, absSum, Nat.cast_add]
      rw [ih B (by simpa using h)]
      have key : (((a - b : ℕ) : ℤ) + ((b - a : ℕ) : ℤ)) = |(a:ℤ) - (b:ℤ)| := by
        rcases le_total a b with hab | hab
        · rw [abs_of_nonpos (by omega)]; omega
        · rw [abs_of_nonneg (by omega)]; omega
      rw [key]

theorem tm1_of_tm1D (A B : List ℕ) (h : A.length = B.length) (hc : tm1D A B = true) :
    tm1 (List.zipWith (fun (a b : ℕ) => (a:ℤ) - (b:ℤ)) A B) = true := by
  rcases A with _ | ⟨a₀, _ | ⟨a₁, as⟩⟩ <;> rcases B with _ | ⟨b₀, _ | ⟨b₁, bs⟩⟩ <;>
    simp only [tm1D, Bool.false_eq_true] at hc <;> simp at h
  · simp only [decide_eq_true_eq] at hc
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, tm1, decide_eq_true_eq]
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [List.zipWith_cons_cons, tm1, decide_eq_true_eq]
    rw [← absDiffSum_cast as bs h, lt_min_iff]
    omega

namespace NP

theorem evalN_append_zeros (A : List ℕ) (n x : ℕ) :
    evalN (A ++ List.replicate n 0) x = evalN A x := by
  induction A with
  | nil =>
    simp only [List.nil_append, evalN]
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, evalN, ih]; simp
  | cons a A ih => simp [evalN, ih]

theorem evalQ_append_zeros (A : List ℕ) (n : ℕ) (x : ℚ) :
    evalQ (A ++ List.replicate n 0) x = evalQ A x := by
  induction A with
  | nil =>
    simp only [List.nil_append, evalQ]
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, evalQ, ih]; simp
  | cons a A ih => simp [evalQ, ih]

theorem length_scaleN (e : ℕ) (A : List ℕ) : (scaleN e A).length = A.length := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [scaleN, ih]

theorem evalN_mono (A : List ℕ) {x x' : ℕ} (hx : x ≤ x') : evalN A x ≤ evalN A x' := by
  induction A with
  | nil => simp [evalN]
  | cons a A ih => simp only [evalN]; exact Nat.add_le_add_left (Nat.mul_le_mul hx ih) a

/-- The scaled polynomial at `2^e x`. -/
theorem evalN_scaleN_pow (e x : ℕ) (A : List ℕ) :
    evalN (scaleN e A) (2 ^ e * x) = 2 ^ (e * (A.length - 1)) * evalN A x := by
  induction A with
  | nil => simp [scaleN, evalN]
  | cons c cs ih =>
    simp only [scaleN, evalN, ih, List.length_cons, Nat.add_sub_cancel]
    rcases cs with _ | ⟨d, ds⟩
    · simp [scaleN, evalN]
    · simp only [List.length_cons, Nat.add_sub_cancel]
      rw [show e * (ds.length + 1) = e * ds.length + e by ring, pow_add]; ring

theorem evalN_scaleN_le (e k : ℕ) (A : List ℕ) (hk : k + 1 ≤ 2 ^ e) :
    evalN (scaleN e A) (k + 1) ≤ 2 ^ (e * (A.length - 1)) * evalN A 1 := by
  calc evalN (scaleN e A) (k + 1) ≤ evalN (scaleN e A) (2 ^ e * 1) := evalN_mono _ (by simpa using hk)
    _ = _ := evalN_scaleN_pow e 1 A

end NP

/-- One dyadic interval `[k/2^e, (k+1)/2^e]`, read off the packed polynomial `r` (base `X`, at most
`L` coefficients): the coefficients of `t ↦ 2^{e(L−1)} q((k + t)/2^e)` are the base-`Y` digits of
`2^{e(L−1)} r.pos` minus those of `2^{e(L−1)} r.neg`, with `Y = 2^e X − k`. -/
def tm1Y (r : PP) (X L k e : ℕ) : Bool :=
  let s := 2 ^ (e * (L - 1))
  let Y := 2 ^ e * X - k
  decide (k + 1 ≤ 2 ^ e) && decide (s * r.pos1 < Y) && decide (s * r.neg1 < Y) &&
    tm1D (NP.digits Y L (s * r.pos)) (NP.digits Y L (s * r.neg))

theorem tm1Y_sound {X L : ℕ} {r : PP} {q : IPoly} (hr : PP.Rep X L r q) (k e : ℕ)
    (hc : tm1Y r X L k e = true) (y : ℚ) (hy0 : (k:ℚ) / 2 ^ e ≤ y)
    (hy1 : y ≤ ((k:ℚ) + 1) / 2 ^ e) : 0 < eval q y := by
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := hr
  simp only [tm1Y, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hk, hp⟩, hn⟩, htm⟩ := hc
  set s := 2 ^ (e * (L - 1)) with hs
  set Y := 2 ^ e * X - k with hY
  set A' := A ++ List.replicate (L - A.length) 0 with hA'def
  set B' := B ++ List.replicate (L - B.length) 0 with hB'def
  have hA' : A'.length = L := by simp only [hA'def, List.length_append, List.length_replicate]; omega
  have hB' : B'.length = L := by simp only [hB'def, List.length_append, List.length_replicate]; omega
  set RA := NP.scaleN e A' with hRA
  set RB := NP.scaleN e B' with hRB
  have hlA : RA.length = L := by rw [hRA, NP.length_scaleN, hA']
  have hlB : RB.length = L := by rw [hRB, NP.length_scaleN, hB']
  have hbA : NP.evalN RA (k + 1) < Y := by
    calc NP.evalN RA (k + 1) ≤ 2 ^ (e * (A'.length - 1)) * NP.evalN A' 1 :=
          NP.evalN_scaleN_le e k A' hk
      _ = s * r.pos1 := by rw [hA', hA'def, NP.evalN_append_zeros, h3]
      _ < Y := hp
  have hbB : NP.evalN RB (k + 1) < Y := by
    calc NP.evalN RB (k + 1) ≤ 2 ^ (e * (B'.length - 1)) * NP.evalN B' 1 :=
          NP.evalN_scaleN_le e k B' hk
      _ = s * r.neg1 := by rw [hB', hB'def, NP.evalN_append_zeros, h4]
      _ < Y := hn
  have hkY : k + Y = 2 ^ e * X := by omega
  have hdA : ∀ i < L, (NP.digits Y L (s * r.pos)).getD i 0 = (NP.shiftN RA k).getD i 0 := by
    have hv : s * r.pos = NP.evalN RA (k + Y) := by
      rw [hkY, hRA, NP.evalN_scaleN_pow, hA', hA'def, NP.evalN_append_zeros, h1]
    rw [hv]; exact digits_shift RA k L hlA.le Y hbA
  have hdB : ∀ i < L, (NP.digits Y L (s * r.neg)).getD i 0 = (NP.shiftN RB k).getD i 0 := by
    have hv : s * r.neg = NP.evalN RB (k + Y) := by
      rw [hkY, hRB, NP.evalN_scaleN_pow, hB', hB'def, NP.evalN_append_zeros, h2]
    rw [hv]; exact digits_shift RB k L hlB.le Y hbB
  have h2e : (0:ℚ) < 2 ^ e := by positivity
  set t := y * 2 ^ e - k with ht
  have ht0 : 0 ≤ t := by rw [div_le_iff₀ h2e] at hy0; linarith
  have ht1 : t ≤ 1 := by rw [le_div_iff₀ h2e] at hy1; linarith
  have hl : (NP.digits Y L (s * r.pos)).length = (NP.digits Y L (s * r.neg)).length := by
    rw [PP.length_digits, PP.length_digits]
  have hQ := tm1_sound _ (tm1_of_tm1D _ _ hl htm) t ht0 ht1
  rw [eval_zipWith_sub _ _ hl,
    list_eq_of_getD L (PP.length_digits _ _ _) ((NP.length_shiftN RA k).trans hlA.le) hdA t,
    list_eq_of_getD L (PP.length_digits _ _ _) ((NP.length_shiftN RB k).trans hlB.le) hdB t,
    NP.evalQ_shiftN, NP.evalQ_shiftN, hRA, hRB, NP.evalQ_scaleN, NP.evalQ_scaleN, hA', hB',
    hA'def, hB'def, NP.evalQ_append_zeros, NP.evalQ_append_zeros] at hQ
  have hy : ((k:ℕ):ℚ) + t = y * 2 ^ e := by rw [ht]; ring
  rw [hy, mul_div_cancel_right₀ _ h2e.ne', ← mul_sub, ← h5] at hQ
  exact pos_of_mul_pos_right hQ (by positivity)

/-- Positivity on `[k₀/2^{e₀}, 1]` over contiguous dyadic intervals `(k, e)` (as `posOn`). -/
def posOnY (r : PP) (X L : ℕ) : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | k₀, e₀, [] => decide (k₀ = 2 ^ e₀)
  | k₀, e₀, (k, e) :: rest =>
      decide (k₀ * 2 ^ e = k * 2 ^ e₀) && tm1Y r X L k e && posOnY r X L (k + 1) e rest

theorem posOnY_sound {X L : ℕ} {r : PP} {q : IPoly} (hr : PP.Rep X L r q) :
    ∀ (k₀ e₀ : ℕ) (l : List (ℕ × ℕ)), posOnY r X L k₀ e₀ l = true →
      ∀ y : ℚ, (k₀:ℚ) / 2 ^ e₀ ≤ y → y ≤ 1 → l ≠ [] → 0 < eval q y := by
  intro k₀ e₀ l
  induction l generalizing k₀ e₀ with
  | nil => intro _ y _ _ h; exact absurd rfl h
  | cons ke rest ih =>
    obtain ⟨k, e⟩ := ke
    intro hc y hy0 hy1 _
    simp only [posOnY, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hk, htm⟩, hrest⟩ := hc
    have h2 : (0:ℚ) < 2 ^ e := by positivity
    have h20 : (0:ℚ) < 2 ^ e₀ := by positivity
    have hstart : (k₀:ℚ) / 2 ^ e₀ = (k:ℚ) / 2 ^ e := by
      rw [div_eq_div_iff h20.ne' h2.ne']; exact_mod_cast hk
    rw [hstart] at hy0
    cases rest with
    | nil =>
      simp only [posOnY, decide_eq_true_eq] at hrest
      have h1 : ((k:ℚ) + 1) / 2 ^ e = 1 := by
        rw [div_eq_one_iff_eq h2.ne']; exact_mod_cast hrest
      exact tm1Y_sound hr k e htm y hy0 (by rw [h1]; exact hy1)
    | cons ke' rest' =>
      rcases le_total y (((k:ℚ) + 1) / 2 ^ e) with hy | hy
      · exact tm1Y_sound hr k e htm y hy0 hy
      · exact ih (k + 1) e hrest y (by push_cast; exact hy) hy1 (by simp)

/-- Every Bernstein coefficient of the dyadic leaf box is positive on `y ∈ [0, 1]`; `cp` are the
packed inputs (shared by the tree). -/
def leafZ (cp : Fin 4 → Fin 4 → PP) (X L ka m kb n : ℕ) (br : List (List (ℕ × ℕ))) : Bool :=
  (List.finRange 4).all fun I => (List.finRange 4).all fun J =>
    let l := br.getD (4 * I.val + J.val) []
    !l.isEmpty && posOnY (pb33 cp ka m kb n I J) X L 0 0 l

theorem leafZ_sound (c : Fin 4 → Fin 4 → IPoly) (cp : Fin 4 → Fin 4 → PP) (X L : ℕ)
    (hcp : ∀ i j, PP.Rep X L (cp i j) (c i j)) (ka m kb n : ℕ) (br : List (List (ℕ × ℕ)))
    (hc : leafZ cp X L ka m kb n br = true) (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (I J : Fin 4) :
    0 < bern33 (fun i j => eval (c i j) y) ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m) ((kb:ℚ) / 2 ^ n)
      (1 / 2 ^ n) I J := by
  simp only [leafZ, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.not_eq_true'] at hc
  obtain ⟨hne, hpos⟩ := hc I J
  have hrep := rep_pb33 hcp ka m kb n I J
  have h := posOnY_sound hrep 0 0 _ hpos y (by simpa using hy0) hy1
    (by intro h; rw [h] at hne; simp at hne)
  rw [eval_ib33] at h
  have hk : (0:ℚ) < 9 * ((2:ℚ) ^ m) ^ 3 * ((2:ℚ) ^ n) ^ 3 := by positivity
  exact pos_of_mul_pos_right h hk.le

def treeZ (cp : Fin 4 → Fin 4 → PP) (X L : ℕ) : UTreeI → ℕ → ℕ → ℕ → ℕ → Bool
  | .leaf br, ka, m, kb, n => leafZ cp X L ka m kb n br
  | .u l r, ka, m, kb, n => treeZ cp X L l (2*ka) (m+1) kb n && treeZ cp X L r (2*ka+1) (m+1) kb n
  | .p l r, ka, m, kb, n => treeZ cp X L l ka m (2*kb) (n+1) && treeZ cp X L r ka m (2*kb+1) (n+1)

theorem treeZ_sound (c : Fin 4 → Fin 4 → IPoly) (cp : Fin 4 → Fin 4 → PP) (X L : ℕ)
    (hcp : ∀ i j, PP.Rep X L (cp i j) (c i j)) (T : UTreeI) :
    ∀ (ka m kb n : ℕ), treeZ cp X L T ka m kb n = true →
      ∀ y : ℚ, 0 ≤ y → y ≤ 1 → ∀ u p : ℝ, (ka:ℝ) / 2 ^ m ≤ u → u ≤ ((ka:ℝ) + 1) / 2 ^ m →
        (kb:ℝ) / 2 ^ n ≤ p → p ≤ ((kb:ℝ) + 1) / 2 ^ n →
        0 < ∑ i : Fin 4, ∑ j : Fin 4, ((eval (c i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
  induction T with
  | leaf br =>
    intro ka m kb n hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    have hs : (0:ℝ) < 1 / 2 ^ m := by positivity
    have ht : (0:ℝ) < 1 / 2 ^ n := by positivity
    apply bicubic_pos (fun i j => ((eval (c i j) y : ℚ) : ℝ)) (a := (ka:ℝ) / 2 ^ m) (s := 1 / 2 ^ m)
      (b := (kb:ℝ) / 2 ^ n) (t := 1 / 2 ^ n) hs ht hu0 (by rw [← add_div]; exact hu1) hp0
      (by rw [← add_div]; exact hp1)
    intro I J
    have h := leafZ_sound c cp X L hcp ka m kb n br hc y hy0 hy1 I J
    have hcast := bern33_cast (fun i j => eval (c i j) y) ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m)
      ((kb:ℚ) / 2 ^ n) (1 / 2 ^ n) I J
    push_cast at hcast
    rw [← hcast]
    exact_mod_cast h
  | u l r ihl ihr =>
    intro ka m kb n hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    simp only [treeZ, Bool.and_eq_true] at hc
    have h2 : (0:ℝ) < 2 ^ m := by positivity
    rcases le_total u ((((2 * ka : ℕ) : ℝ) + 1) / 2 ^ (m + 1)) with hu | hu
    · refine ihl (2*ka) (m+1) kb n hc.1 y hy0 hy1 u p ?_ hu hp0 hp1
      rw [pow_succ]; push_cast
      calc (2 * (ka:ℝ)) / (2 ^ m * 2) = (ka:ℝ) / 2 ^ m := by field_simp
        _ ≤ u := hu0
    · refine ihr (2*ka+1) (m+1) kb n hc.2 y hy0 hy1 u p ?_ ?_ hp0 hp1
      · push_cast at hu ⊢; exact hu
      · rw [pow_succ]; push_cast
        calc u ≤ ((ka:ℝ) + 1) / 2 ^ m := hu1
          _ = (2 * (ka:ℝ) + 1 + 1) / (2 ^ m * 2) := by field_simp; ring
  | p l r ihl ihr =>
    intro ka m kb n hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    simp only [treeZ, Bool.and_eq_true] at hc
    have h2 : (0:ℝ) < 2 ^ n := by positivity
    rcases le_total p ((((2 * kb : ℕ) : ℝ) + 1) / 2 ^ (n + 1)) with hp | hp
    · refine ihl ka m (2*kb) (n+1) hc.1 y hy0 hy1 u p hu0 hu1 ?_ hp
      rw [pow_succ]; push_cast
      calc (2 * (kb:ℝ)) / (2 ^ n * 2) = (kb:ℝ) / 2 ^ n := by field_simp
        _ ≤ p := hp0
    · refine ihr ka m (2*kb+1) (n+1) hc.2 y hy0 hy1 u p hu0 hu1 ?_ ?_
      · push_cast at hp ⊢; exact hp
      · rw [pow_succ]; push_cast
        calc p ≤ ((kb:ℝ) + 1) / 2 ^ n := hp1
          _ = (2 * (kb:ℝ) + 1 + 1) / (2 ^ n * 2) := by field_simp; ring

/-- The HIGH tree check with packed interval tests: base `X` and length bound `L` are data. -/
def checkZ (c : Fin 4 → Fin 4 → IPoly) (X L : ℕ) (T : UTreeI) : Bool :=
  decide (maxLen16 c ≤ L) && treeZ (fun i j => PP.pack X (c i j)) X L T 0 0 0 1

theorem checkZ_sound (c : Fin 4 → Fin 4 → IPoly) (X L : ℕ) (T : UTreeI)
    (hc : checkZ c X L T = true) (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (u p : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    0 < ∑ i : Fin 4, ∑ j : Fin 4, ((eval (c i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
  simp only [checkZ, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact treeZ_sound c _ X L
    (fun i j => PP.rep_pack X L (c i j) ((length_le_maxLen16 c i j).trans hc.1)) T 0 0 0 1 hc.2
    y hy0 hy1 u p (by simpa using hu0) (by simpa using hu1) (by simpa using hp0)
    (by norm_num; linarith)

end IPoly

namespace Pk

open IPoly

/-- Phase 1 with the packing base `X` as data (no first pass at `X = 1`): the packed coefficients,
read back at base `X`, are `g` times the data `cK`. -/
def decKgX (Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (g X : ℕ) (cK : Fin 4 → Fin 4 → IPoly) :
    Bool :=
  decide (0 < Δ) && decide (0 < g) &&
  ((List.finRange 4).all fun a => (List.finRange 4).all fun j =>
    (alignedK X Δ eIn P b k a j).ok && decide ((alignedK X Δ eIn P b k a j).pos1 < X) &&
      decide ((alignedK X Δ eIn P b k a j).neg1 < X) &&
      decide (unpack X (alignedK X Δ eIn P b k a j) = IPoly.smul g (cK a j)))

theorem coeffPos_of_decKgX_of (Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (g X : ℕ)
    (cK : Fin 4 → Fin 4 → IPoly) (hd : decKgX Δ eIn P b k g X cK = true)
    (hpos : ∀ y : ℚ, 0 ≤ y → y ≤ 1 → ∀ u p : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ p → p ≤ 1/2 →
      0 < ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ)) :
    HighCoeffPos (P.highU b k) := by
  intro y hy0 hy1 u p hu0 hu1 hp0 hp1
  simp only [decKgX, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at hd
  obtain ⟨⟨hΔ, hg⟩, hall⟩ := hd
  have h := hpos y hy0 hy1 u p hu0 hu1 hp0 hp1
  set E := maxE16 (fun a j => highUZ X Δ eIn P b k a j) with hE
  have heq : ∀ i j, (g : ℝ) * ((IPoly.eval (cK i j) y : ℚ) : ℝ) =
      ((Δ : ℝ) ^ E) * ((Poly.eval (P.highU b k i j) y : ℚ) : ℝ) := by
    intro i j
    have hrep : Rep X Δ (alignedK X Δ eIn P b k i j) (P.highU b k i j) :=
      rep_scale _ (rep_highUZ eIn P b k i j)
    obtain ⟨⟨⟨hok, hp⟩, hn⟩, hcK⟩ := hall i j
    have h1 := eval_unpack hrep hok hp hn y
    rw [hcK, IPoly.eval_smul] at h1
    have he : (alignedK X Δ eIn P b k i j).e = E := by
      have := le_maxE16 (fun a j => highUZ X Δ eIn P b k a j) i j
      simp only [alignedK, scale, ← hE] at this ⊢; omega
    rw [he] at h1
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at h2 ⊢
    exact h2
  have hgpos : (0:ℝ) < g := by exact_mod_cast hg
  have hsum : (g : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) *
      u ^ (i:ℕ) * p ^ (j:ℕ) = ((Δ : ℝ) ^ E) * ∑ i : Fin 4, ∑ j : Fin 4,
        ((Poly.eval (P.highU b k i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
    simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, heq i j]
  have hΔE : (0:ℝ) < (Δ : ℝ) ^ E := by positivity
  have hprod : 0 < (g : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ((IPoly.eval (cK i j) y : ℚ) : ℝ) *
      u ^ (i:ℕ) * p ^ (j:ℕ) := mul_pos hgpos (by simpa using h)
  rw [hsum] at hprod
  exact pos_of_mul_pos_right hprod hΔE.le

/-- Phases 1 and 2 with both bases as data: `decKgX` and the packed tree check `IPoly.checkZ`. -/
theorem coeffPos_of_decKgXZ (Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (g X : ℕ)
    (cK : Fin 4 → Fin 4 → IPoly) (XZ L : ℕ) (T : IPoly.UTreeI)
    (hd : decKgX Δ eIn P b k g X cK = true) (ht : IPoly.checkZ cK XZ L T = true) :
    HighCoeffPos (P.highU b k) :=
  coeffPos_of_decKgX_of Δ eIn P b k g X cK hd (IPoly.checkZ_sound cK XZ L T ht)

/-- Phases 1 and 2 with the packed tree check (`IPoly.checkZ`). -/
theorem coeffPos_of_decKgZ (Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (g : ℕ)
    (cK : Fin 4 → Fin 4 → IPoly) (X L : ℕ) (T : IPoly.UTreeI) (hd : decKg Δ eIn P b k g cK = true)
    (ht : IPoly.checkZ cK X L T = true) : HighCoeffPos (P.highU b k) :=
  coeffPos_of_decKg_of Δ eIn P b k g cK hd (IPoly.checkZ_sound cK X L T ht)

end Pk

end QRH.RepeatedMarks.Faceless
