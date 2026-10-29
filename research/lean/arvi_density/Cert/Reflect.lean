/- Reflective certificates of the marked HIGH gate `HybridGatesM.high_marked`.

For a density step with rational parameters `S`, the scaled cleared marked gate of branch `k`,
`F_k(v,t,p) = cNumY_k − r · E · cDenY_k` (`E = densE`, `ν = nuT v t = Y/E`), is a polynomial of
degree ≤ 2 in `t` and ≤ 3 in `p` whose coefficients are polynomials in `v`. `fOf S (brk S)` (`Fpoly`)
computes it from `S` by exact polynomial arithmetic (PR 76's `Poly`, here in three layers `v`, `p`,
`t`), and `eval_Fpoly` shows once, for all parameters, that it evaluates to `F_k`. Rescaled to `v = vmax·y`
and cleared to integers, positivity on `y ∈ [0,1], t ∈ [0,1], p ∈ [0,1/2]` is PR 76's
kernel-checked `checkZ` (`Faceless/TreeZ.lean`, `checkZ_sound`); `checkZ` is stated for rational
`y`, and continuity in `v` extends it to every real `v`. `high_marked_of_checks` assembles the six
branches into the field `high_marked`, so a step certificate is six `decide +kernel` checks instead
of per-step `ring` identities and Bernstein boxes. -/
import Submissions.arvi_density.Source.HybridGatesMarked
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.TreeZ

set_option autoImplicit false

namespace QRH.ArviDensity.Reflect

open QRH.RepeatedMarks.Faceless QRH.ArviDensity.Hybrid

/-! ### Real evaluation of `Poly` (the variable `v`) -/

/-- `Poly.eval` at a real point. -/
def evalR : Poly → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * evalR cs x

@[simp] theorem evalR_nil (x : ℝ) : evalR [] x = 0 := rfl
@[simp] theorem evalR_cons (c : ℚ) (cs : Poly) (x : ℝ) :
    evalR (c :: cs) x = (c : ℝ) + x * evalR cs x := rfl

theorem evalR_add (p q : Poly) (x : ℝ) : evalR (Poly.add p q) x = evalR p x + evalR q x := by
  induction p generalizing q with
  | nil => simp [Poly.add]
  | cons a p ih =>
    cases q with
    | nil => simp [Poly.add]
    | cons b q => simp only [Poly.add, evalR_cons, ih]; push_cast; ring

theorem evalR_smul (c : ℚ) (p : Poly) (x : ℝ) : evalR (Poly.smul c p) x = (c : ℝ) * evalR p x := by
  induction p with
  | nil => simp [Poly.smul]
  | cons a p ih =>
    simp only [Poly.smul, List.map_cons, evalR_cons] at ih ⊢
    rw [ih]; push_cast; ring

theorem evalR_mul (p q : Poly) (x : ℝ) : evalR (Poly.mul p q) x = evalR p x * evalR q x := by
  induction p with
  | nil => simp [Poly.mul]
  | cons a p ih =>
    simp only [Poly.mul, evalR_add, evalR_smul, evalR_cons, ih]
    push_cast; ring

theorem evalR_cast (p : Poly) (y : ℚ) : evalR p (y : ℝ) = ((Poly.eval p y : ℚ) : ℝ) := by
  induction p with
  | nil => simp
  | cons c p ih => simp [ih]

theorem continuous_evalR (p : Poly) : Continuous (evalR p) := by
  induction p with
  | nil => exact continuous_const
  | cons c p ih => exact continuous_const.add (continuous_id.mul ih)

/-! ### Polynomials in `p` with coefficients in `Poly` -/

abbrev P2 := List Poly

namespace P2

def add : P2 → P2 → P2
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => Poly.add a b :: add p q

def smul (c : Poly) (p : P2) : P2 := p.map (Poly.mul c)

def mul : P2 → P2 → P2
  | [], _ => []
  | a :: p, q => add (smul a q) ([] :: mul p q)

/-- `Σ_j evalR (P j) v · x^j`. -/
def eval : P2 → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, v, x => evalR c v + x * eval cs v x

@[simp] theorem eval_nil (v x : ℝ) : eval [] v x = 0 := rfl
@[simp] theorem eval_cons (c : Poly) (cs : P2) (v x : ℝ) :
    eval (c :: cs) v x = evalR c v + x * eval cs v x := rfl

theorem eval_add (p q : P2) (v x : ℝ) : eval (add p q) v x = eval p v x + eval q v x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp only [add, eval_cons, evalR_add, ih]; ring

theorem eval_smul (c : Poly) (p : P2) (v x : ℝ) : eval (smul c p) v x = evalR c v * eval p v x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, List.map_cons, eval_cons, evalR_mul] at ih ⊢
    rw [ih]; ring

theorem eval_mul (p q : P2) (v x : ℝ) : eval (mul p q) v x = eval p v x * eval q v x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    simp only [mul, eval_add, eval_smul, eval_cons, evalR_nil, ih]
    ring

theorem continuous_eval (p : P2) (x : ℝ) : Continuous (fun v => eval p v x) := by
  induction p with
  | nil => exact continuous_const
  | cons c p ih => exact (continuous_evalR c).add (continuous_const.mul ih)

/-- `Σ_{j < n} evalR (P j) v · x^j` for `P` of length at most `n`. -/
theorem eval_eq_sum (p : P2) (n : ℕ) (h : p.length ≤ n) (v x : ℝ) :
    eval p v x = ∑ j ∈ Finset.range n, evalR (p.getD j []) v * x ^ j := by
  induction p generalizing n with
  | nil => simp
  | cons c p ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ', eval_cons, ih m (by simp at h; omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end P2

/-! ### Polynomials in `t` with coefficients in `P2` -/

abbrev P3 := List P2

namespace P3

def add : P3 → P3 → P3
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => P2.add a b :: add p q

def smul (c : P2) (p : P3) : P3 := p.map (P2.mul c)

def mul : P3 → P3 → P3
  | [], _ => []
  | a :: p, q => add (smul a q) ([] :: mul p q)

/-- Multiplication by a rational constant. -/
def cmul (c : ℚ) (p : P3) : P3 := smul [[c]] p

def sub (p q : P3) : P3 := add p (cmul (-1) q)

/-- `Σ_i P2.eval (P i) v x · t^i`. -/
def eval : P3 → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | c :: cs, v, t, x => P2.eval c v x + t * eval cs v t x

@[simp] theorem eval_nil (v t x : ℝ) : eval [] v t x = 0 := rfl
@[simp] theorem eval_cons (c : P2) (cs : P3) (v t x : ℝ) :
    eval (c :: cs) v t x = P2.eval c v x + t * eval cs v t x := rfl

theorem eval_add (p q : P3) (v t x : ℝ) : eval (add p q) v t x = eval p v t x + eval q v t x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp only [add, eval_cons, P2.eval_add, ih]; ring

theorem eval_smul (c : P2) (p : P3) (v t x : ℝ) :
    eval (smul c p) v t x = P2.eval c v x * eval p v t x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, List.map_cons, eval_cons, P2.eval_mul] at ih ⊢
    rw [ih]; ring

theorem eval_mul (p q : P3) (v t x : ℝ) : eval (mul p q) v t x = eval p v t x * eval q v t x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    simp only [mul, eval_add, eval_smul, eval_cons, P2.eval_nil, ih]
    ring

theorem eval_cmul (c : ℚ) (p : P3) (v t x : ℝ) : eval (cmul c p) v t x = (c : ℝ) * eval p v t x := by
  simp [cmul, eval_smul]

theorem eval_sub (p q : P3) (v t x : ℝ) : eval (sub p q) v t x = eval p v t x - eval q v t x := by
  simp only [sub, eval_add, eval_cmul]; push_cast; ring

theorem continuous_eval (p : P3) (t x : ℝ) : Continuous (fun v => eval p v t x) := by
  induction p with
  | nil => exact continuous_const
  | cons c p ih => exact (P2.continuous_eval c x).add (continuous_const.mul ih)

theorem eval_eq_sum (p : P3) (n m : ℕ) (h : p.length ≤ n) (hrow : ∀ r ∈ p, r.length ≤ m)
    (v t x : ℝ) :
    eval p v t x = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
      evalR ((p.getD i []).getD j []) v * t ^ i * x ^ j := by
  induction p generalizing n with
  | nil => simp
  | cons c p ih =>
    obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ', eval_cons,
      ih n' (by simp at h; omega) (fun r hr => hrow r (List.mem_cons_of_mem _ hr)),
      P2.eval_eq_sum c m (hrow c (by simp)) v x]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, Finset.mul_sum]
    rw [add_comm]
    congr 1
    all_goals
      try (refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring)

end P3

/-! ### The gate polynomial of a step -/

/-- The rational parameters of a marked density step: parent `G(B0, L0, c0)`, child `(B, L)`, selection
`A, D`, gate reserve `r`. -/
structure StepQ where
  B0 : ℚ
  L0 : ℚ
  c0 : ℚ
  B : ℚ
  L : ℚ
  A : ℚ
  D : ℚ
  r : ℚ

namespace StepQ
variable (S : StepQ)

/-- The crossing `s₀ = (B0 - B)/(L0 - L)`. -/
def s0 : ℚ := (S.B0 - S.B) / (S.L0 - S.L)
/-- `densK L0 A`. -/
def K : ℚ := 999 / 1000 * S.L0 * S.A
/-- `1 + D v`. -/
def Xv : Poly := [1, S.D]
/-- `A v`. -/
def Av : Poly := [0, S.A]
/-- `width = s₀ + v`. -/
def Wv : Poly := [S.s0, 1]
/-- `densE = (L0 - L)(1 + D v) + (6 B0 - L0) A`. -/
def Ev : Poly := [(S.L0 - S.L) + (6 * S.B0 - S.L0) * S.A, (S.L0 - S.L) * S.D]

end StepQ

/-- A polynomial in `v` as a constant in `(t, p)`. -/
def lv (q : Poly) : P3 := [[q]]
/-- A rational constant. -/
def lc (c : ℚ) : P3 := [[[c]]]
/-- The variable `t`. -/
def tP : P3 := [[], [[1]]]
/-- The variable `p`. -/
def pP : P3 := [[[], [1]]]

@[simp] theorem eval_lv (q : Poly) (v t x : ℝ) : P3.eval (lv q) v t x = evalR q v := by
  simp [lv]
@[simp] theorem eval_lc (c : ℚ) (v t x : ℝ) : P3.eval (lc c) v t x = (c : ℝ) := by
  simp [lc]
@[simp] theorem eval_tP (v t x : ℝ) : P3.eval tP v t x = t := by
  simp [tP]
@[simp] theorem eval_pP (v t x : ℝ) : P3.eval pP v t x = x := by
  simp [pP]

/-- `Y = K (1 - t) + 3/4 t E`, the numerator of `ν = nuT v t = Y/E`. -/
def Ypoly (S : StepQ) : P3 :=
  P3.add (lc S.K) (P3.mul tP (P3.sub (P3.cmul (3 / 4) (lv S.Ev)) (lc S.K)))

/-- The scaled cleared gate `cNumY − r · E · cDenY` of a branch with data `(U, αU, βU, eU)`. -/
def Fpoly (S : StepQ) (U aU bU eU : P3) : P3 :=
  let X := lv S.Xv
  let AV := lv S.Av
  let W := lv S.Wv
  let E := lv S.Ev
  let Y := Ypoly S
  let XA6 := P3.sub X (P3.cmul 6 AV)
  let WXA := P3.sub (P3.mul W X) AV
  let five := P3.sub (P3.cmul 5 E) (P3.cmul 6 Y)
  let den := P3.add (P3.sub (P3.cmul (15 / 2) (P3.mul E U)) (P3.cmul 3 (P3.mul Y U))) (P3.mul five eU)
  let t1 := P3.mul Y (P3.add (P3.cmul 5 (P3.mul (P3.mul XA6 U) E))
    (P3.mul five (P3.add (P3.mul aU WXA) (P3.mul bU XA6))))
  let one2p := P3.sub (lc 1) (P3.cmul 2 pP)
  let t2 := P3.mul (P3.mul Y (P3.sub (P3.mul one2p WXA)
    (P3.sub (P3.mul (P3.sub (lc S.B) (P3.mul (lc (S.L - 1)) W)) X) AV))) den
  let t3 := P3.mul (P3.mul E AV) den
  P3.sub (P3.add (P3.add t1 t2) t3) (P3.cmul S.r (P3.mul (P3.mul E X) den))

/-- The one-time identity: `Fpoly` evaluates to the scaled cleared gate `cNumY − r · E · cDenY`. -/
theorem eval_Fpoly (S : StepQ) (U aU bU eU : P3) (v t x : ℝ) :
    P3.eval (Fpoly S U aU bU eU) v t x =
      cNumY (S.A : ℝ) (S.D : ℝ) v x (width (S.B0 : ℝ) (S.L0 : ℝ) (S.B : ℝ) (S.L : ℝ) v) (S.B : ℝ)
          (S.L : ℝ) (P3.eval U v t x) (P3.eval aU v t x) (P3.eval bU v t x) (P3.eval eU v t x)
          (densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
            3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)
          (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v) -
        (S.r : ℝ) * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v *
          cDenY (S.D : ℝ) v (P3.eval U v t x) (P3.eval eU v t x)
            (densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
              3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)
            (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v) := by
  simp only [Fpoly, Ypoly, P3.eval_add, P3.eval_sub, P3.eval_mul, P3.eval_cmul, eval_lv, eval_lc,
    eval_tP, eval_pP, StepQ.Xv, StepQ.Av, StepQ.Wv, StepQ.Ev, StepQ.K, StepQ.s0, evalR_cons,
    evalR_nil]
  simp only [cNumY, cDenY, width, cross, densE, densK]
  push_cast
  ring

/-! ### The six branches (`gHighM_ij`) -/

/-- `(U, αU, βU, eU)` of branch `(0,0)`: `(1, 17p, 0, 0)`. -/
def br00 (_S : StepQ) : P3 × P3 × P3 × P3 := (lc 1, P3.cmul 17 pP, [], [])
/-- Branch `(0,1)`: `(1, 16p, c0 p, 0)`. -/
def br01 (S : StepQ) : P3 × P3 × P3 × P3 := (lc 1, P3.cmul 16 pP, P3.cmul S.c0 pP, [])
/-- Branch `(0,2)`: `(L0 - 2p, 16p(L0 - 2p), B0 p, p)`. -/
def br02 (S : StepQ) : P3 × P3 × P3 × P3 :=
  let u := P3.sub (lc S.L0) (P3.cmul 2 pP)
  (u, P3.cmul 16 (P3.mul pP u), P3.cmul S.B0 pP, pP)
/-- Branch `(1,0)`: `(1 - p, p(1 - p), p, p)`. -/
def br10 (_S : StepQ) : P3 × P3 × P3 × P3 :=
  let u := P3.sub (lc 1) pP
  (u, P3.mul pP u, pP, pP)
/-- Branch `(1,1)`: `(1 - p, 0, p + c0 p (1 - p), p)`. -/
def br11 (S : StepQ) : P3 × P3 × P3 × P3 :=
  let u := P3.sub (lc 1) pP
  (u, [], P3.add pP (P3.cmul S.c0 (P3.mul pP u)), pP)
/-- Branch `(1,2)`: `((1-p)(L0-2p), 0, p(L0-2p) + B0 p(1-p), p(L0-2p) + p(1-p))`. -/
def br12 (S : StepQ) : P3 × P3 × P3 × P3 :=
  let u := P3.sub (lc 1) pP
  let w := P3.sub (lc S.L0) (P3.cmul 2 pP)
  (P3.mul u w, [], P3.add (P3.mul pP w) (P3.cmul S.B0 (P3.mul pP u)),
    P3.add (P3.mul pP w) (P3.mul pP u))

/-- The gate polynomial of a branch. -/
def fOf (S : StepQ) (b : P3 × P3 × P3 × P3) : P3 := Fpoly S b.1 b.2.1 b.2.2.1 b.2.2.2

/-! ### The kernel check and its soundness -/

/-- The coefficient of `t^i p^j` (a polynomial in `v`). -/
def coefF (P : P3) (i j : Fin 4) : Poly := (P.getD i []).getD j []

/-- `y ↦ q (a y)`. -/
def scaleArg (a : ℚ) : Poly → Poly
  | [] => []
  | c :: cs => c :: Poly.smul a (scaleArg a cs)

theorem eval_scaleArg (a : ℚ) (q : Poly) (y : ℚ) : Poly.eval (scaleArg a q) y = Poly.eval q (a * y) := by
  induction q with
  | nil => simp [scaleArg]
  | cons c cs ih => simp only [scaleArg, Poly.eval_cons, Poly.eval_smul, ih]; ring

/-- At most four coefficients in `t` and in `p`. -/
def degOK (P : P3) : Bool := decide (P.length ≤ 4) && P.all (fun r => decide (r.length ≤ 4))

/-- The integer coefficients `Dn · q(vmax · y)` of `t^i p^j`. -/
def intC (P : P3) (a : ℚ) (Dn : ℕ) (i j : Fin 4) : IPoly := IPoly.ofPoly (scaleArg a (coefF P i j)) Dn

/-- The certificate check of one branch: degrees, integrality, and PR 76's tree check. -/
def checkF (P : P3) (a : ℚ) (Dn X L : ℕ) (T : IPoly.UTreeI) : Bool :=
  degOK P && decide (0 < Dn) &&
    (List.finRange 4).all (fun i => (List.finRange 4).all (fun j =>
      IPoly.isIntMul (scaleArg a (coefF P i j)) Dn)) &&
    IPoly.checkZ (intC P a Dn) X L T

theorem eval_eq_fin_sum (P : P3) (h : degOK P = true) (v t x : ℝ) :
    P3.eval P v t x = ∑ i : Fin 4, ∑ j : Fin 4, evalR (coefF P i j) v * t ^ (i : ℕ) * x ^ (j : ℕ) := by
  simp only [degOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rw [P3.eval_eq_sum P 4 4 h.1 h.2 v t x]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range 4,
    evalR ((P.getD i []).getD j []) v * t ^ i * x ^ j) 4]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => evalR ((P.getD i []).getD j []) v * t ^ (i : ℕ) * x ^ j) 4]
  rfl

/-- A passed check: the gate polynomial is positive at `v = a·y` for every rational `y ∈ [0,1]`. -/
theorem checkF_sound (P : P3) (a : ℚ) (Dn X L : ℕ) (T : IPoly.UTreeI) (hc : checkF P a Dn X L T = true)
    (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (t x : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / 2) : 0 < P3.eval P ((a : ℝ) * (y : ℝ)) t x := by
  simp only [checkF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at hc
  obtain ⟨⟨⟨hdeg, hD⟩, hint⟩, hz⟩ := hc
  have hpos := IPoly.checkZ_sound (intC P a Dn) X L T hz y hy0 hy1 t x ht0 ht1 hx0 hx1
  have hterm : ∀ i j : Fin 4, ((IPoly.eval (intC P a Dn i j) y : ℚ) : ℝ) =
      (Dn : ℝ) * evalR (coefF P i j) ((a : ℝ) * (y : ℝ)) := by
    intro i j
    rw [intC, IPoly.eval_ofPoly _ _ (hint i j), eval_scaleArg,
      show ((a : ℝ) * (y : ℝ)) = ((a * y : ℚ) : ℝ) by push_cast; ring, evalR_cast]
    push_cast; ring
  simp only [hterm] at hpos
  rw [eval_eq_fin_sum P hdeg]
  have hsum : ∑ i : Fin 4, ∑ j : Fin 4, (Dn : ℝ) * evalR (coefF P i j) ((a : ℝ) * (y : ℝ)) *
      t ^ (i : ℕ) * x ^ (j : ℕ) = (Dn : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4,
        evalR (coefF P i j) ((a : ℝ) * (y : ℝ)) * t ^ (i : ℕ) * x ^ (j : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum] at hpos
  have hDpos : (0 : ℝ) < Dn := by exact_mod_cast hD
  exact pos_of_mul_pos_right hpos hDpos.le

/-- A function continuous on `ℝ` that is positive at the rationals of `[0,1]` is nonnegative on `[0,1]`. -/
theorem nonneg_of_rat_pos {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ y : ℚ, 0 ≤ y → y ≤ 1 → 0 < g y) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ g x := by
  let u : ℕ → ℚ := fun n => (⌊x * (n + 1)⌋₊ : ℚ) / (n + 1)
  have hu : ∀ n : ℕ, ((u n : ℚ) : ℝ) = (⌊x * (n + 1)⌋₊ : ℝ) / (n + 1) := by
    intro n; simp [u]
  have hlo : ∀ n : ℕ, x - 1 / ((n : ℝ) + 1) ≤ ((u n : ℚ) : ℝ) := by
    intro n
    rw [hu]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hn]
    have := Nat.lt_floor_add_one (x * ((n : ℝ) + 1))
    have e : (x - 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = x * ((n : ℝ) + 1) - 1 := by field_simp
    rw [e]; linarith
  have hhi : ∀ n : ℕ, ((u n : ℚ) : ℝ) ≤ x := by
    intro n
    rw [hu]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hn]
    exact Nat.floor_le (by positivity)
  have hu0 : ∀ n : ℕ, 0 ≤ u n := by
    intro n; simp only [u]; positivity
  have hu1 : ∀ n : ℕ, u n ≤ 1 := by
    intro n
    have := hhi n
    exact_mod_cast this.trans hx1
  have hlim : Filter.Tendsto (fun n : ℕ => ((u n : ℚ) : ℝ)) Filter.atTop (nhds x) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) := tendsto_const_nhds
    have h1 : Filter.Tendsto (fun n : ℕ => x - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds x) := by
      simpa using hc.sub h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlo hhi
  have hcl : IsClosed {z : ℝ | 0 ≤ g z} := isClosed_le continuous_const hg
  exact hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => (h (u n) (hu0 n) (hu1 n)).le)

/-- A passed check: the gate polynomial is nonnegative on `[0, a] × [0,1] × [0,1/2]`. -/
theorem nonneg_of_checkF (P : P3) (a : ℚ) (Dn X L : ℕ) (T : IPoly.UTreeI)
    (hc : checkF P a Dn X L T = true) (ha : 0 < a) (v t x : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 0 ≤ P3.eval P v t x := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hg : Continuous (fun y : ℝ => P3.eval P ((a : ℝ) * y) t x) :=
    (P3.continuous_eval P t x).comp (continuous_const.mul continuous_id)
  have h := nonneg_of_rat_pos hg (fun y hy0 hy1 => checkF_sound P a Dn X L T hc y hy0 hy1 t x ht0 ht1
    hx0 hx1) (v / a) (div_nonneg hv0 ha'.le) (by rw [div_le_one ha']; exact hv1)
  simpa [mul_div_cancel₀ v ha'.ne'] using h

/-! ### From a passed check to the marked HIGH gate -/

open QRH.RepeatedMarks in
/-- One branch: a passed check gives `r ≤ gHighM` at `ν = nuT v t`. The branch data evaluate to the
`(U, αU, βU, eU)` of `hcl` (`hU`–`heU`). -/
theorem branch_ge_of_check (S : StepQ) (b : P3 × P3 × P3 × P3) (k : Branch) (a : ℚ) (Dn X L : ℕ)
    (T : IPoly.UTreeI) (hc : checkF (fOf S b) a Dn X L T = true) (ha : 0 < a)
    {v t p U aU bU eU : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1 / 2)
    (hU : P3.eval b.1 v t p = U) (haU : P3.eval b.2.1 v t p = aU) (hbU : P3.eval b.2.2.1 v t p = bU)
    (heU : P3.eval b.2.2.2 v t p = eU)
    (hE : 0 < densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)
    (hcl : gHighM (S.B0 : ℝ) (S.L0 : ℝ) (S.c0 : ℝ) (S.B : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v
        ((densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
            3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v) /
          densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v) p k *
        (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v *
          cDenY (S.D : ℝ) v U eU (densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
            3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)
            (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)) =
      cNumY (S.A : ℝ) (S.D : ℝ) v p (width (S.B0 : ℝ) (S.L0 : ℝ) (S.B : ℝ) (S.L : ℝ) v) (S.B : ℝ)
        (S.L : ℝ) U aU bU eU (densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
            3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)
        (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v))
    (hD : 0 < densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v *
          cDenY (S.D : ℝ) v U eU (densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
            3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)
            (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)) :
    (S.r : ℝ) ≤ gHighM (S.B0 : ℝ) (S.L0 : ℝ) (S.c0 : ℝ) (S.B : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v
      (nuT (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v t) p k := by
  have hF := nonneg_of_checkF (fOf S b) a Dn X L T hc ha v t p hv0 hv1 ht0 ht1 hp0 hp1
  rw [fOf, eval_Fpoly, hU, haU, hbU, heU] at hF
  rw [nuT_eq hE.ne']
  have h1 : (S.r : ℝ) * (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v *
          cDenY (S.D : ℝ) v U eU (densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
            3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)
            (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)) ≤
      gHighM (S.B0 : ℝ) (S.L0 : ℝ) (S.c0 : ℝ) (S.B : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v
        ((densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
            3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v) /
          densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v) p k *
        (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v *
          cDenY (S.D : ℝ) v U eU (densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
            3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)
            (densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v)) := by
    rw [hcl]; linarith [hF]
  exact le_of_mul_le_mul_right h1 hD

open QRH.RepeatedMarks in
/-- The marked HIGH field `high_marked` of a step from six passed branch checks. The real parameters
are the casts of `S` (`hB0r` … `hDr`), `a` is the excess range `c - s₀`, and the remaining hypotheses
are the step's own scalar gates (`sel_den_pos`, `dens_den_pos`, `q_lower`, `q_upper`,
`retained_width`, `H_lower`). -/
theorem high_marked_of_checks (S : StepQ) {B0 L0 c0 B L c A D : ℝ}
    (hB0r : (S.B0 : ℝ) = B0) (hL0r : (S.L0 : ℝ) = L0) (hc0r : (S.c0 : ℝ) = c0) (hBr : (S.B : ℝ) = B)
    (hLr : (S.L : ℝ) = L) (hAr : (S.A : ℝ) = A) (hDr : (S.D : ℝ) = D)
    (a : ℚ) (hvmax : c - cross B0 L0 B L = (a : ℝ)) (ha : 0 < a) (hr : 0 < S.r)
    (hB0 : 22 / 23 ≤ B0) (hB1 : B0 ≤ 1) (hL0 : 1 < L0) (hc0 : 0 ≤ c0) (hc1 : c0 ≤ 1)
    (hx : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → 0 < 1 + D * v)
    (hE : ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → 0 < densE B0 L0 L A D v)
    (hql : UnifPos (gQLower B0 L0 L A D) 0 (c - cross B0 L0 B L))
    (hqu : UnifPos (gQUpper B0 L0 L A D) 0 (c - cross B0 L0 B L))
    (hrw : UnifPos (gRetainedWidth B0 L0 B L A D) 0 (c - cross B0 L0 B L))
    (hhl : UnifPos (gHLower A D) 0 (c - cross B0 L0 B L))
    (X Lz D00 D01 D02 D10 D11 D12 : ℕ) (T00 T01 T02 T10 T11 T12 : IPoly.UTreeI)
    (h00 : checkF (fOf S (br00 S)) a D00 X Lz T00 = true)
    (h01 : checkF (fOf S (br01 S)) a D01 X Lz T01 = true)
    (h02 : checkF (fOf S (br02 S)) a D02 X Lz T02 = true)
    (h10 : checkF (fOf S (br10 S)) a D10 X Lz T10 = true)
    (h11 : checkF (fOf S (br11 S)) a D11 X Lz T11 = true)
    (h12 : checkF (fOf S (br12 S)) a D12 X Lz T12 = true) :
    ∃ r : ℝ, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ c - cross B0 L0 B L → ∀ ν,
      dens B0 L0 L A D v ≤ ν → ν ≤ 3 / 4 →
        r ≤ highJ B L (width B0 L0 B L v) (sel A D v) ν +
          Source.gainC ν B0 L0 c0 (width B0 L0 B L v - sel A D v) (packed A D v) := by
  subst hB0r hL0r hc0r hBr hLr hAr hDr
  refine ⟨(S.r : ℝ), by exact_mod_cast hr, fun v h0 h1 ν hν1 hν2 => ?_⟩
  have hva : v ≤ (a : ℝ) := hvmax ▸ h1
  obtain ⟨r2, hr2, hu⟩ := hqu
  have hb := hu v h0 h1
  unfold gQUpper at hb
  have hq34 : dens (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v < 3 / 4 := by linarith
  obtain ⟨t, ht0, ht1, hνt⟩ := exists_nuT hq34 hν1 hν2
  obtain ⟨r1, hr1, hl⟩ := hql
  have hql' := hl v h0 h1
  unfold gQLower at hql'
  have hm := nuT_mem (by linarith) hq34 ht0 ht1
  rw [← hνt] at hm
  obtain ⟨r3, hr3, hw3⟩ := hrw
  have hS := hw3 v h0 h1
  unfold gRetainedWidth at hS
  obtain ⟨r4, hr4, hh4⟩ := hhl
  have hQ := hh4 v h0 h1
  unfold gHLower at hQ
  have hEv := hE v h0 h1
  have hxv := hx v h0 h1
  -- `ν = Y/E` and the parameter range of `gHighM_ij`
  have hνYE := nuT_eq (B0 := (S.B0 : ℝ)) (L0 := (S.L0 : ℝ)) (L := (S.L : ℝ)) (A := (S.A : ℝ))
    (D := (S.D : ℝ)) (v := v) (t := t) hEv.ne'
  have hm' := hm
  rw [hνt, hνYE] at hm'
  have hY : densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
      3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v ≤
      3 / 4 * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v := by
    have := hm'.2
    rwa [div_le_iff₀ hEv] at this
  have branch : ∀ p : ℝ, 0 ≤ p → p ≤ 1 / 2 → ∀ k : Branch,
      (S.r : ℝ) ≤ gHighM (S.B0 : ℝ) (S.L0 : ℝ) (S.c0 : ℝ) (S.B : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v
        (nuT (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v t) p k := by
    intro p hp0 hp1
    have P : Params ((densK (S.L0 : ℝ) (S.A : ℝ) * (1 - t) +
        3 / 4 * t * densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v) /
        densE (S.B0 : ℝ) (S.L0 : ℝ) (S.L : ℝ) (S.A : ℝ) (S.D : ℝ) v) p 8 (S.B0 : ℝ) (S.L0 : ℝ)
        (S.c0 : ℝ) :=
      ⟨by linarith [hm'.1], hm'.2, hp0, hp1, by norm_num, hB0, hB1, hL0, hc0, hc1⟩
    have hDs := cDenY_pos_all hxv hEv hY hp0 hp1 hL0
    have hx' : 1 + (S.D : ℝ) * v ≠ 0 := hxv.ne'
    apply forall_branch
    · exact branch_ge_of_check S (br00 S) (0, 0) a D00 X Lz T00 h00 ha h0 hva ht0 ht1 hp0 hp1
        (by simp [br00]) (by simp [br00, P3.eval_cmul] <;> ring) (by simp [br00]) (by simp [br00]) hEv
        (gHighM_scaled hEv.ne' (gHighM_00 _ _ _ _ _ _ _ v _ p P hx')) hDs.1
    · exact branch_ge_of_check S (br01 S) (0, 1) a D01 X Lz T01 h01 ha h0 hva ht0 ht1 hp0 hp1
        (by simp [br01]) (by simp [br01, P3.eval_cmul] <;> ring) (by simp [br01, P3.eval_cmul] <;> ring)
        (by simp [br01]) hEv
        (gHighM_scaled hEv.ne' (gHighM_01 _ _ _ _ _ _ _ v _ p P hx')) hDs.1
    · exact branch_ge_of_check S (br02 S) (0, 2) a D02 X Lz T02 h02 ha h0 hva ht0 ht1 hp0 hp1
        (by simp [br02, P3.eval_sub, P3.eval_cmul])
        (by simp [br02, P3.eval_sub, P3.eval_cmul, P3.eval_mul] <;> ring)
        (by simp [br02, P3.eval_cmul] <;> ring) (by simp [br02]) hEv
        (gHighM_scaled hEv.ne' (gHighM_02 _ _ _ _ _ _ _ v _ p P hx')) hDs.2.1
    · exact branch_ge_of_check S (br10 S) (1, 0) a D10 X Lz T10 h10 ha h0 hva ht0 ht1 hp0 hp1
        (by simp [br10, P3.eval_sub]) (by simp [br10, P3.eval_sub, P3.eval_mul])
        (by simp [br10]) (by simp [br10]) hEv
        (gHighM_scaled hEv.ne' (gHighM_10 _ _ _ _ _ _ _ v _ p P hx')) hDs.2.2.1
    · exact branch_ge_of_check S (br11 S) (1, 1) a D11 X Lz T11 h11 ha h0 hva ht0 ht1 hp0 hp1
        (by simp [br11, P3.eval_sub]) (by simp [br11])
        (by simp [br11, P3.eval_add, P3.eval_sub, P3.eval_cmul, P3.eval_mul] <;> ring) (by simp [br11])
        hEv (gHighM_scaled hEv.ne' (gHighM_11 _ _ _ _ _ _ _ v _ p P hx')) hDs.2.2.1
    · exact branch_ge_of_check S (br12 S) (1, 2) a D12 X Lz T12 h12 ha h0 hva ht0 ht1 hp0 hp1
        (by simp [br12, P3.eval_sub, P3.eval_cmul, P3.eval_mul]) (by simp [br12])
        (by simp [br12, P3.eval_add, P3.eval_sub, P3.eval_cmul, P3.eval_mul] <;> ring)
        (by simp [br12, P3.eval_add, P3.eval_sub, P3.eval_cmul, P3.eval_mul] <;> ring) hEv
        (gHighM_scaled hEv.ne' (gHighM_12 _ _ _ _ _ _ _ v _ p P hx')) hDs.2.2.2
  have hfac := le_gainC_of_facets (ν := ν) (B := (S.B0 : ℝ)) (lam := (S.L0 : ℝ)) (h := (S.c0 : ℝ))
    (S := width (S.B0 : ℝ) (S.L0 : ℝ) (S.B : ℝ) (S.L : ℝ) v - sel (S.A : ℝ) (S.D : ℝ) v)
    (Q := packed (S.A : ℝ) (S.D : ℝ) v)
    (r := (S.r : ℝ) - highJ (S.B : ℝ) (S.L : ℝ) (width (S.B0 : ℝ) (S.L0 : ℝ) (S.B : ℝ) (S.L : ℝ) v)
      (sel (S.A : ℝ) (S.D : ℝ) v) ν)
    (by linarith [hm.1]) hν2 hB0 hB1 hL0 hc0 hc1 (by linarith) (by linarith)
    (fun p hp0 hp1 k => by
      have := branch p hp0 hp1 k
      rw [← hνt] at this
      unfold gHighM at this
      linarith)
  linarith

end QRH.ArviDensity.Reflect
