# R1 — exact amplifier identities over ℤ[ω]: classification, numerics, Lean map

Scope: item list of the R1 brief (cross factor, dilation table, vanishing, pools, other identities, Lean map).
Everything below was re-derived and re-checked from the Lean *definitions* (not from earlier notes). Scripts and raw output:
`r1/` (`bash r1/run_all.sh` regenerates `r1/results.txt`, about 3.5 minutes; numpy + mpmath).
I did not run Lean. Status tags used throughout: **[L]** = a theorem with that statement exists in the Lean files I read (named, file given; not recompiled here); **[L+]** = follows from such theorems by short glue that is
not yet written as a lemma; **[N]** = own derivation, backed only by numerics (counts given); nothing tagged [N] should be used as established.

## 0. Verdict in twelve lines

1. **Cross factor, any block.** For primary coprime `B, n`: `g(B n,h) = ε(B,n)·χ_n(B)²·g(B,h)·g(n,h)`. The cubic part is `χ_n(B)²`; the *only* quadratic
   part is the ray sign `ε(B,n)=±1` (a function of `B mod 4, n mod 4`). No Jacobi symbol `(B/n)₂` appears. [L: `crossFactor_primary`,
   `gauss_primary_power_product`, `normalized_coprime_product`]. So the "twist `χ_n(fD)²`" of the working notes is **`ε(fD,n)·χ_n(fD)²`**; the sign is real (it is −1 for 3/8 of all class pairs).
2. **Exact dilation of a block `D^m`:** `g(D^m n,h) = ε(D,n)^m·g(D^m,h)·g(n,D^{4m}h)`, i.e. the minimal exponent is `k(m)=4m mod 6 = 4,2,0,4,2,0` for `m=1..6`
   (cost `k/m = 4, 1, 0, 1, 2/5, 0` per unit of selected volume). [identity: L+; table: N, 20 605 comparisons, 0 failures]
3. **Claim (a)** (squared block, cubic twist, `D²` exact): **true**, no sign at all (`ε²=1`): `g(D²n,h)=g(D²,h)·g(n,D²h)`. Twist = `χ_n(D)⁴ = (D/n)₃⁻¹`.
4. **Claim (b)** ("`D¹` leaves `(D/n)₂`"): **false as written**, correct form: `D¹` leaves `(n/D)₂ = χ_D(n)³ = ε(D,n)·(D/n)₂`, the Dirichlet character of `n` mod `D`
   (this is exactly the kernel `quadraticRow` of the library's quadratic sieve). It equals `(D/n)₂` only when `ε(D,n)=+1` (304 of 500 random pairs).
5. **Claim (c)** (`D⁴` smallest exact dilation of a simple block): **true up to the ray sign** `ε(D,n)`; exact on the nose iff `D ≡ cube root of unity mod 4`
   or after the bounded correction of item 6.
6. **New exact identity: the ray sign is a bounded dilation.** `ε(B,n) = (E₀/n)₂ = χ_n(E₀)³` with `E₀ ∈ {1,−1,λ,−λ}` determined by `B mod 4`
   (`B ≡ ζ·E₀`, `ζ³=1`). Hence **`g(B n,h) = g(B,h)·g(n, E_B h)`, `E_B = E₀(B)³·∏ p^{(4 m_p mod 6)}`, with no leftover twist at all.** Cost of the correction: `N(E₀³) ∈ {1,27}`.
   This replaces the ray-character expansion of the sign (`firstPhaseTable_expansion`, mass bound 256) by a single common vector and four bounded evaluation points. [N: 307+98+366 cases double precision, 40 cases at 40 digits, finite 12×12 table exact]
7. **Non-coprime n:** `g(n,D^s h) = χ_n(D)^{[−s]} g(n,h)` (`χ⁶:=` coprimality mask) holds for *all* h iff `D,n` are coprime or **some** common prime `p | gcd(n,D)` has `6 ∤ v_p(n)` and `v_p(n) ≤ s·v_p(D)`
   (the right side is a product of local factors, one vanishing factor suffices). So for `D` prime `FifthFree` is exactly the condition for `s=4`, for a composite `D` it is needed at one common prime only, and for `s=2` the condition is cube-freeness there.
8. **Block scalars are spiky:** `g(D^m,h) ≠ 0 ⇔ v_D(h)=m−1` (6∤m; *exactly* `D^{m−1}∥h`, not `D^{m−1}|h`; for m=6: `v_D(h)≥5`), `|gaussRow| = N(D)^{(m−1)/2}`. Mean square over one period is `1−1/N` for every `m` (Parseval; checked N=7, m≤3 and N=13, m≤2: the sup is exactly `N^{(m−1)/2}`),
   so the height is paid for by a support of density `N(D)^{−(m−1)}`: for m ≥ 2 each frequency `h` sees only the primes `D` with `D^{m−1}∥h` (≤ ω(h) of them), not a whole family.
9. **Pools:** `g(u,p⁶h)=1_{p∤u}g(u,h)` holds for all `u` with `v_p(u) ≤ 5` (Lean has squarefree-at-p only). `p^k`, `k=1..5`, is *not* a copy: on `p∤u` it multiplies by `χ_u(p)^{−k}`
   (k=3 quadratic, k=2,4 cubic, k=1,5 sextic), and it keeps exactly the columns with `v_p(u)=k+1`; `p∥u` never survives any `k≥1`; `p²∥u` survives only at `k=1`.
10. **Cube and sixth-power blocks need no dilation:** `g(D³n,h)=ε(D,n)g(D³,h)g(n,h)` (exactly multiplicative when `D ≡ ζ mod 4`), `g(D⁶n,h)=g(D⁶,h)g(n,h)`.
11. **Bi-dilation (symmetric) form:** `g(D^m n,h) = g(D^m, n^j h)·g(n, D^k h)` is exact iff `m(j−1)` even and `k ≡ −m(j+2) (mod 6)`; for `m=1`: `(j,k) ∈ {(1,3),(3,1),(5,5)}` mod 6, sign absorbed with no bounded element.
12. Further exact laws (conjugation, unit orbits, supplements, Kummer/Hasse–Davenport/Stickelberger evaluations of the block scalars) are in §3.5; they are context, not amplifiers.

## 1. Conventions (exactly the Lean's)

* `O = ℤ[ω]`, `ω = e^{2πi/3}` (`eisEmbedding ω = omega3`), `λ = ω−1` (the prime over 3; `√−3 = 1+2ω = −ωλ`), `2` is inert (norm 4, residue field `F₄`).
* `Supported(s)`: `s≠0` and every prime factor `P` of `(s)` has `λ∉P` and `char(O/P)≠2`, i.e. **`s` is prime to 6**; *not* squarefree, *not* primary. At `λ` (N=3) and `2` (N=4)
  no sextic character exists (6 ∤ N−1), which is why they are excluded; elements `±1,ω,2,λ` are allowed as **dilations** (they are prime to every column).
* *Primary* = `λ² | s−1` ⇔ `s ≡ 1 (mod 3)`; unique generator of an ideal prime to 3 (`primaryGenerator`). Sextic symbols depend only on the ideal; `sexticGauss` depends on the generator:
  `g(us,h)=χ_s(u)g(s,h)` for a unit `u` [N, 237 cases; one-line from unit scale]. All columns below are primary generators.
* `(x/P)₆` = the `ζ∈μ₆(O)` with `ζ ≡ x^{(N P−1)/6} (mod P)` (`sexticChar = cubicChar²·quadraticChar`), `χ_s(x) := idealRowHom x (span s) = ∏_{P^e∥s}(x/P)₆^e` (0 if not coprime).
  Write `c_n(x)=χ_n(x)²` (cubic symbol `(x/n)₃`, `idealRowHom_square`) and `s_n(x)=χ_n(x)³=(x/n)₂` (Jacobi symbol of `x` modulo `n`). Then `χ = s·c⁻¹`.
* `ψ_s(x) = exp(2πi·Tr_{K/ℚ}(x/(s√−3)))` = `exp(2πi·[ω-coordinate of x·s̄]/N(s))` (`quotientTrace`), `g(s,h)=Σ_{d mod s}χ_s(d)ψ_s(hd)` (`sexticGauss`), `gaussRow = g/√N(s)`.
* Ray sign `ε(a,b) := sexticReciprocityPhase a b = quadraticRaySign(a mod 4, b mod 4) ∈ {±1}` for odd `a,b`. Lean: `idealRowHom_primary_reciprocity a b`: **`χ_a(b) = ε(a,b)·χ_b(a)`** (a,b primary, supported).
  Consequences: `c_n(D)=c_D(n)` (cubic reciprocity), `s_D(n)=ε(D,n)s_n(D)`, i.e. `ε = (D/n)₂(n/D)₂`; `ε` is symmetric, bimultiplicative, `ε²=1`.
  **Closed form [N, all 144 pairs]:** write `B ≡ ζ(1+2x_B) (mod 4)`, `ζ∈μ₃`, `x_B∈F₄=O/2`; then `ε(B,n)=(−1)^{Tr_{F₄/F₂}(x_B x_n)}`. `ε(B,·)≡1` iff `B ≡ 1,ω,ω² (mod 4)` (3 of 12 classes);
  `ε=−1` on 54 of the 144 class pairs (3/8).
* Fixed notation below: `D` primary prime (split or inert), `N=N(D)`, `n` primary, coprime to `D`; `m` = multiplicity of the block `B=D^m`.

I re-implemented all of this (`r1/zw.py`) and validated it against **Lean theorems** first (`r1/t0_basics.py`): `sexticGauss_unit_scale` (2787 cases, incl. non-primary `b`),
`sexticGauss_coprime_product` (187), `idealRowHom_primary_reciprocity` (586; all 144 class pairs, 3349 more in `v_final.py`), `fourth_power` (500, 14 non-coprime), `square_twist` of
`arvi_mixed_step` (200). All pass, so the objects tested are the Lean's objects.

## 2. Master table

`k` = exponent of the dilation `D^k` applied to the residual frequency, `m` = multiplicity of the removed block, cost = `k/m` (frequency growth per unit of selected log-volume; the pool has no selected volume,
its cost is 6 per pool-prime width). "scalar" = `g(D^m,h)`: support and normalised size. κ = exponent of the residual relative to the block-free frequency `H'` (`h=D^{m−1}H'`), see §3.2.

| ID | amplifier | exact identity | twist left over | dilation, cost k/m (κ mod 6) | scalar, support | numerics | status |
|---|---|---|---|---|---|---|---|
| U | unit scale, any `E` prime to `n` | `g(n,Eh)=χ_n(E)⁻¹g(n,h)` | – | – | – | 2787 | **[L]** `sexticGauss_unit_scale` |
| P6 | pool (Collet) | `g(u,p⁶h)=1_{p∤u}·g(u,h)`, `v_p(u)≤5`; composite `E`: `g(u,E⁶h)=1_{(E,u)=1}g(u,h)` | none | `p⁶`, 6 per pool width | – | grid 1265+234; 207; 40 digits | **[L]** squarefree at p (`sexticGauss_pool_prime_mask`), coprime (`gauss_sixth_frequency`); `v_p∈2..5` **[L+]** |
| Pk | valuation selector `p^k`, k=1..5, p∤h | `p∤u`: `g(u,p^kh)=χ_u(p)^{−k}g(u,h)`; `v_p(u)=i≥1`: nonzero iff `i=k+1`, then `=ε(p,u')^iχ_{u'}(p)^{i+1}·g(p^i,p^{k}h)g(u',h)` | `p∤u`: k=3 quad `(p/u)₂`; k=2,4 cubic; k=1,5 sextic; survivors `i=k+1`: k=0 `εc`, 1 `Q`, 2 `εC`, 3 `S`, 4 `ε` | `p^k` | `g(p^i,p^{i−1}h')=N^{i−1}χ_p(h')^{−i}G_i(p)` | 1265 + 95 ratios | local table **[L]**; assembly **[L+]** |
| T1 | simple block (Sil) | `g(Dn,h)=ε(D,n)·g(D,h)·g(n,D⁴h)` | `ε(D,n)` only | `D⁴`, **4** (κ=4) | `‖gaussRow‖=1`, `D∤h` | 500 + 293 (norms to 1500) | **[L]** `normalized_coprime_product`+`fourth_power`/`whole_column`; sign: see C |
| T1′ | simple block, light | `g(Dn,h)=(n/D)₂·g(D,h)·g(n,Dh)` | `(n/D)₂ = ε(D,n)(D/n)₂` (quadratic sieve kernel) | `D¹`, **1** | as T1 | 500/500; 40 digits | **[L+]** |
| T2 | squared block | `g(D²n,h)=g(D²,h)·g(n,D²h)`, equivalently `g(D²n,DH')=(D/n)₂·g(D²,DH')g(n,H')` | **none** | `D²`, **1** (κ=3) | `D∥h`, `gaussRow(D²,DH')=G₂(D;H')`, a cubic Gauss sum of modulus `√N` | 450 + 58; 25 at 40 digits | **[L]** H'-form `square_twist` (arvi_mixed_step); h-form **[L+]** |
| T3 | cube block | `g(D³n,h)=ε(D,n)·g(D³,h)·g(n,h)` | `ε(D,n)` only (absent if `D≡ζ mod 4`) | none, **0** (κ=2) | `D²∥h`, `‖gaussRow‖=N`, quadratic Gauss sum, explicit (§3.5.5) | 350 + 15; 10 at 40 digits | **[L+]** |
| T4 | 4th-power block | `g(D⁴n,h)=g(D⁴,h)·g(n,D⁴h)` | none | `D⁴`, **1** (κ=1) | `D³∥h`, `N^{3/2}` | 200 | **[L+]** |
| T5 | 5th-power block | `g(D⁵n,h)=ε(D,n)·g(D⁵,h)·g(n,D²h)` | `ε(D,n)` only | `D²`, **2/5** (κ=0: residual undilated in `H'`) | `D⁴∥h`, `N²` | 60 | **[L+]** (outside `FifthFree`) |
| T6 | 6th-power block | `g(D⁶n,h)=g(D⁶,h)·g(n,h)` | none | none, **0** (κ=5) | `v_D(h)≥5`: `−N²` (=5), `N²(N−1)` (≥6) | 25 | **[L+]** |
| Tm | any `m`, unreduced | `g(D^m n,h)=ε(D,n)^m g(D^m,h) g(n,D^{4m}h)` | `ε^m` | `D^{4m}≡D^{4m mod 6}` (n prime to D) | – | 1585 | **[L+]** (`crossFactor_primary`+unit scale) |
| C | sign absorber | `ε(B,n)=(E₀/n)₂`, so `g(Bn,h)=g(B,h)g(n,E_B h)` | **none** | `E_B=E₀³∏p^{4m_p mod 6}`; extra norm 1 or 27 | – | 307+98+366; 12×12 exact; 40 digits | **[N]** (ingredients [L]: `lambdaQuadraticTable`, `idealRowHom_lambda_cube`, `quadraticRaySign`) |
| BD | bi-dilation | `g(D^mn,h)=g(D^m,n^jh)g(n,D^kh)` iff `m(j−1)` even, `k≡−m(j+2)` | none | `n^j`, `D^k` | – | 900 cases × 144 cells | **[L+]** |
| M | several blocks `∏D_i^{m_i}` | all of the above, exponent-wise | `ε(B,n)=∏ε^{m_i}` | `∏D_i^{4m_i mod 6}` | scalars multiply | 815 + 228 + 98 | **[L+]** (`sexticReciprocityPhase_mul_*`) |
| W | whole column with sign | `Σ_vB_v1[(D,a_v)=1]gaussRow(D^ma_v,k)=gaussRow(D^m,k)Σ_vB_v gaussRow(a_v,E_Bk)` for `v_p(a_v)≤κ`, `6∤v_p` | none | as above | – | 614 inside; 45/45 fail outside | **[N]** (Sil's `selected_row_fourth` is the E₀=1, ray-expanded version) |

Cost summary: exact residual dilation per unit of selected volume `k/m = 4, 1, 0, 1, 2/5, 0` for `m=1..6`; with the free variable `H'` the residual exponent is `κ = (5−m) mod 6 = 4,3,2,1,0,5`.
For a product block the costs average: `Σ k(m_i) log N(D_i) / Σ m_i log N(D_i)`.

## 3. Details

### 3.1 CRT cross factor (item 1)

`g(Bn,h)=χ_B(n)χ_n(B)·g(B,h)g(n,h)` [L, `sexticGauss_coprime_product`; no primary hypothesis]. For primary `B,n`, reciprocity gives `χ_B(n)=ε(B,n)χ_n(B)`, so

    cross(B,n) = ε(B,n) · χ_n(B)^2 ,     B = D^m :   ε(D,n)^m · χ_n(D)^{2m} = ε(D,n)^m · c_n(D)^m .

* cubic part `c^m` (order 3; `χ_n(D)^{2m}=χ_D(n)^{2m}` by cubic reciprocity, either modulus works);
* quadratic part **`ε(D,n)^m`**, a ±1 depending only on `D,n mod 4`; trivial for even `m`. There is no `(D/n)₂` in the cross factor.
* `m=1`: `εc`; `m=2`: `c² = c⁻¹` (purely cubic); `m=3`: `ε` (the `χ⁶` is the coprimality mask, `idealRowHom_sixth_eq_mask`); `m=4`: `c`; `m=5`: `εc²`; `m=6`: `1`.
* Lean: [L] `crossFactor_primary`, `gauss_primary_power_product`, `residualCharacter_moving` (Moments/AmplificationShortening: any primary `p`, any `k`; `residualCharacter p k u = ε(p,u)^k·χ_p(u)^{2k} = ε(p,u)^k·χ_u(p)^{2k}`), and for general primary `d`
  `normalized_coprime_product` (Sil, MixedSelectedCommon): `gaussRow(d a) = ε(d,a)χ_a(d)² gaussRow d·gaussRow a`.
* Numerics: `m=1..6`: 500/450/350/200/60/25 random cases (D of norm 7..121, inert `q=5,11`, n with 1–2 primes, exponents ≤2, all with every local Gauss sum non-zero): **1585/1585**, plus 366 cases with `N(D)` up to 1500 and all 12 classes of `D mod 4`; 40-digit check on 40+25+10 cases (max error 4e−40).

### 3.2 Which dilation absorbs what (item 2)

`g(n,D^kh)=χ_n(D)^{−k}g(n,h)`, hence for the block `D^m` (all exponents mod 6; `χ=s·c⁻¹`)

    leftover(m,k) := cross / dilation-twist = ε(D,n)^m · χ_n(D)^{2m+k} = ε(D,n)^m · s_n(D)^k · c_n(D)^{m−k} .

Cubic part cancels iff `k ≡ m (mod 3)`; the rest is `ε^m s^k`. Table (verified in all 78 cells `m=1..6, k=0..12`, **20 605 comparisons, 0 failures**; `1` exact, `e` only the ray sign, `Q` quadratic `χ³`, `C` cubic `χ^{2,4}`, `S` sextic `χ^{1,5}`, prefix `e` = times `ε(D,n)` for odd `m`):

    m\k    1   2   3   4   5   6   7   8   9  10  11  12
    m=1   eQ  eC  eS   e  eS  eC  eQ  eC  eS   e  eS  eC
    m=2    S   1   S   C   Q   C   S   1   S   C   Q   C
    m=3   eS  eC  eQ  eC  eS   e  eS  eC  eQ  eC  eS   e
    m=4    Q   C   S   1   S   C   Q   C   S   1   S   C
    m=5   eS   e  eS  eC  eQ  eC  eS   e  eS  eC  eQ  eC
    m=6    S   C   Q   C   S   1   S   C   Q   C   S   1

Lists of absorbing exponents (the answer to "which `D^k`, k=1..12"); `exact` leaves nothing for even `m` and only the ray sign `ε(D,n)` for odd `m`:

    m   exact       leaves Q (quadratic)   leaves C (cubic)     leaves S (sextic)
    1   4, 10       1, 7                   2, 6, 8, 12          3, 5, 9, 11
    2   2, 8        5, 11                  4, 6, 10, 12         1, 3, 7, 9
    3   6, 12       3, 9                   2, 4, 8, 10          1, 5, 7, 11
    4   4, 10       1, 7                   2, 6, 8, 12          3, 5, 9, 11
    5   2, 8        5, 11                  4, 6, 10, 12         1, 3, 7, 9
    6   6, 12       3, 9                   2, 4, 8, 10          1, 5, 7, 11      (k=0 is also exact for m=3 up to ε and for m=6)

Which quadratic character: for **odd `m`**, `ε·s = χ_D(n)³ = (n/D)₂` (Dirichlet character of `n` mod `D`; library kernel `QuadraticSieve.quadraticRow`), for **even `m`** it is `s = (D/n)₂` (modulus `n`, numerator `D`).
Cubic leftovers are `c^{±1}`: the kernel `CubicSieve.idealKernel` (`idealKernel_reciprocity` makes the modulus irrelevant).

Verdicts on the claims in the brief:
* (a) **True.** `m=2`: twist `χ_n(D)⁴ = c_n(D)⁻¹` (cubic, exponent −1 ≡ 2 in `c`), `D²` exact (k=2, also 8, 14, …). No sign because `ε²=1`. 450/450 (+25 at 40 digits).
* (b) **False as stated** (§0 item 4): leftover of `D¹` is `(n/D)₂=εs`, not `s=(D/n)₂`. Negative control: of 500 random pairs the leftover equals `(n/D)₂` in 500 and `(D/n)₂` in only 304; the 196 failures are exactly `ε=−1`.
* (c) **True up to `ε`**: the exact exponents for `m=1` are `k≡4 (mod 6)` (4, 10), leaving only `ε(D,n)`; `k=1,7` leave `Q`, `k=2,6,8,12` leave `C`, `k=3,5,9,11` leave `S`. Exactness without any leftover needs the correction of §3.5.1. Smallest positive exact exponent is 4 for `m=1`; for the other multiplicities it is 2 (m=2), 0 (m=3), 4 (m=4), 2 (m=5), 0 (m=6).
* Earlier note "4 is the least exponent among transfers of this kind" (BARRIER_REVISITED §5 Q1) holds for **simple** blocks only; it is not a property of the CRT structure.

Free-variable view. The block scalar forces `h = D^{m−1}H'` (`D∤H'`). Relative to `H'` the residual point is `D^{κ}H'`, `κ=k+m−1`, and the leftover is
`ε(D,n)^m·χ_n(D)^{m+κ+1}`; it is exact for `κ ≡ 5−m (mod 6)`: `g(D^mn,D^{m−1}H') = ε(D,n)^m·g(D^m,D^{m−1}H')·g(n,D^{(5−m) mod 6}H')`
[N: 1560/1560 for the exact form, and all 10 920 cells `m=1..5, κ=0..6` below]:

    m\κ     0   1   2   3   4   5   6
    m=1    eC  eQ  eC  eS   e  eS  eC
    m=2     Q   C   S   1   S   C   Q
    m=3    eC  eS   e  eS  eC  eQ  eC
    m=4     S   1   S   C   Q   C   S
    m=5     e  eS  eC  eQ  eC  eS   e
    m=6     S   C   Q   C   S   1   S      (m=6 by the same formula; not sampled separately)

Examples: `m=5`, `κ=0`: `g(D⁵n,D⁴H')=ε(D,n)g(D⁵,D⁴H')g(n,H')` (the residual is not dilated at all); `m=4`, `κ=1`: exact; `m=2`, `κ=0`: exactly `(D/n)₂`
(this is the Lean `square_twist`); `m=2`, `κ=3`: exact. Reducing `κ` mod 6 (i.e. replacing `D^{k}` by `D^{k mod 6}`) is legitimate only with the explicit coprimality mask (§3.3).

### 3.3 Non-coprime residual columns (item 3)

Local table [L: `actualSextic_primePowerGauss_at_pow`, `primePowerGauss_at_pow_nonprincipal/principal`, `sexticGauss_prime_power`; N: 143+111 spot checks, norm-7 prime up to `j=7`]:
for `1≤j`, `p` prime, `h₀` prime to `p`:

    6 ∤ j :  g(p^j, p^v h₀) ≠ 0  ⇔  v = j−1,   |g| = N^{j−1/2}
    6 | j :  g(p^j, p^v h₀) ≠ 0  ⇔  v ≥ j−1,   g = −N^{j−1} (v=j−1),  N^{j−1}(N−1) (v≥j).

Hence, for dilation `D^s`, `g(n,D^sh)=0` for **all `h`** iff some prime `p | gcd(n,D)` has `j=v_p(n)` with `6∤j` and `j ≤ s·v_p(D)` (CRT: the Gauss sum is a product of local factors, and if every common prime admits a non-vanishing frequency one can choose `h` making all of them non-zero). Then
`g(n,D^sh) = χ_n(D)^{[−s]}g(n,h)` holds for every `n` and `h`, both sides being 0 when `D,n` share a prime (here `χ^6 := coprimality mask`, `[−s]∈{1..6}`, `[−s]≡−s`).
Sufficiency was tested on 1048 random cases (0 violations), the existential form on 114 cases with two common primes (`D=pq`, `n=p^iq^j`; 97 predicted-hold all hold, 17 predicted-fail all fail for some `h`); sharpness on every cell of the table below (p of norm 7, `D=p`, `n=p^j`, valuations `v_p(h)=0..j+2` sampled; A = identity holds for every sampled `h`, `.` = it fails for some `h`), and on 124 random cases predicted to fail (48 showed a failure at the 4 sampled `h`):

    s\j   1  2  3  4  5  6  7
    1     A  .  .  .  .  .  .
    2     A  A  .  .  .  .  .
    3     A  A  A  .  .  .  .
    4     A  A  A  A  .  .  .      (= FifthFree, Sil)
    5,6   A  A  A  A  A  .  .
    7..12 A  A  A  A  A  .  A

In the situation of the transfer the block scalar already forces `v_D(h) ≥ m−1`, so the range improves to `v_p(n) ≤ κ=k(m)+m−1`, `6∤v_p(n)`: m=1 → {1..4} (= FifthFree), m=2 → {1,2,3}, m=3 → {1,2}, m=4 → {1..5,7},
m=5 → {1..5}, m=6 → {1..5} (`r1/table_gen.py`). Whole-column check (`e7`, prime `D`; for composite `D` read "at one common prime"): inside the range 614/614 exact, outside 45/45 fail (so the range is sharp). Consequences:
the squared-block transfer is exact on columns that are cube-free (indeed 4th-power-free) at the primes of `D` (compatible with the CubeFree chain); the cube-block identity needs an explicit mask (`k=0` gives none); the 6|j obstruction is why `FifthFree` cannot be relaxed to 6th-power-free for `s=4`.
Lean: `FifthFree` is a global hypothesis of `fifth_free_nonunit_zero`, but its proof picks one common prime `p` and uses `multiplicity p a < 5` only there; the localisation and the `s`-parametrisation are a rewrite of `prime_power_nonunit_zero` ([L+]).

### 3.4 Pools (item 4)

For a pool prime `p` and `H=p^kh`, `p∤h`, column `u=p^iu'` (`p∤u'`) [grid `e4_pools.py`: 234 + 1265 + 95 checks; spot checks 131+630+14; 40-digit: 33]:

| k | `p∤u` (i=0) | `p∥u` (i=1) | `p²∥u` (i=2) | other i |
|---|---|---|---|---|
| 1 | `χ_u(p)⁻¹`, sextic | 0 | **survives**: `(p/u')₂·g(p²,ph)g(u',h)` (quadratic, ratio `ε²χ^{3}`) | i=3..5: 0 |
| 2 | `χ_u(p)⁻²`, cubic | 0 | 0 | i=3 survives (`εc` type, ratio `εχ⁴`) |
| 3 | `χ_u(p)⁻³ = (p/u)₂`, quadratic | 0 | 0 | i=4 survives (ratio `χ⁵`) |
| 4 | `χ_u(p)⁻⁴`, cubic | 0 | 0 | i=5 survives (ratio `ε`) |
| 5 | `χ_u(p)⁻⁵`, sextic | 0 | 0 | i=6 survives (`−N⁵`, ratio `χ`) |
| 6 | **1** (twist-free indicator; Collet) | 0 | 0 | i=6: `N⁵(N−1)`, i=7: surv. |

So `k=6` is the only twist-free indicator among `k=1..6`; `k=3` gives a pure quadratic twist `(p/u)₂` (quadratic sieve), `k=2,4` pure cubic (cubic sieve). Dilation by `p^k` is a *valuation selector*: it keeps `v_p(u)=0` (twisted) and `v_p(u)=k+t+1` (`t=v_p(h)`), kills the rest. Survivor ratio relative to the local Gauss sum and `g(u',h)` is `ε(p,u')^iχ_{u'}(p)^{2i−k}`.

### 3.5 Other exact identities (item 5)

**3.5.1 Ray sign = bounded dilation (C).** Statement [N]: for primary `B` and odd `n`, with `B ≡ ζE₀ (mod 4)`, `ζ∈{1,ω,ω²}`, `E₀∈{1,−1,λ,−λ}`:

    ε(B,n) = (E₀/n)₂ = χ_n(E₀)^3 ,    (−1/n)₂=(−1)^{(N(n)−1)/2},   (λ/n)₂ = lambdaQuadraticTable(n mod 4)  [Lean ThetaNonvanishing].

    E₀ = 1   : B mod 4 ∈ {(1,0),(0,1),(3,3)} = {1,ω,ω²}          (a+bω written (a,b))
    E₀ = −1  : B mod 4 ∈ {(3,0),(0,3),(1,1)} = {−1,−ω,−ω²}        (N(B) ≡ 1 mod 4 in these two rows)
    E₀ = λ   : B mod 4 ∈ {(3,1),(3,2),(2,1)} = {λ,ωλ,ω²λ}
    E₀ = −λ  : B mod 4 ∈ {(1,3),(1,2),(2,3)} = {−λ,−ωλ,−ω²λ}      (N(B) ≡ 3 mod 4 in these two rows)

Finite proof: the exact 12×12 table `quadraticRaySign r s = q_{E₀(r)}(s)` (`v_final.py` V2) built from two class functions of `n mod 4`: `lambdaQuadraticTable` (Lean) and `(−1)^{(N−1)/2}` (not a Lean table yet); both were checked against the actual symbols on 6 primary elements in each of the 12 classes (144 checks). Conceptually: `ε(B,n)` is the dyadic Hilbert symbol `(B,n)₂`;
for `n≡1 mod λ` the product formula gives `(λ/n)₂=(λ,n)₂`; the four classes `x_B∈F₄` are represented by `1` (x=0), `−1` (x=1), `λ` (x=ω²), `−λ` (x=ω), because `λω ≡ 1+2ω² (mod 4)`.
Only these four quadratic classes occur (never anything involving 2: `(2/n)₂=χ₈(N n)` has conductor 8). Rational blocks only ever need `E₀=±1` (`D=q≡1 mod 12`: E₀=1; `q≡7 mod 12`: −1; inert `−q`: E₀=1 iff `q≡3 mod 4`). Conjugation swaps `λ↔−λ` (checked on all 12 classes).
Consequences: (i) `g(Bn,h)=g(B,h)g(n,E_Bh)` exactly; (ii) whole-column form (W) replaces `selected_row_rays` (ray expansion, `firstPhaseTable_mass ≤ 256`) by a *single* common vector and four evaluation points `E₀³D⁴k`;
(iii) restricting the selected primes to `D ≡ ζ (mod 4)` (density 1/4) or the residual columns to `n ≡ ζ (mod 4)` removes `ε` entirely. Cost: `E₀³` has norm 1 or 27, a constant.
Evidence: 307 prime-power blocks (`m=1,3,5`) + 98 composite blocks + 366 cases `N(D)≤1500` (all 12 classes) at double precision, 40 cases at 40 digits (max rel. error 1.7e−40), whole column 614.
Lean: [L+] pieces — `idealRowHom_lambda_cube`, `lambdaQuadraticTable_mul`, `unitSupplement`/`quadraticTwoSupplement` pattern for `χ₄(N)`, `sexticGauss_unit_scale`; one decidable 12×12 lemma and one glue lemma are missing.

**3.5.2 Bi-dilation (BD).** Unit scale on both sides of the CRT: `g(D^m,n^jh)=χ_{D^m}(n)^{−j}g(D^m,h)=ε(D,n)^{mj}χ_n(D)^{−mj}g(D^m,h)`. Matching `ε^mχ^{2m}` gives the rule in the table (verified in all 144 cells `(m, j mod 6, k mod 6)`, 900 cases, 0 violations).
Exact cells mod 6, `(j,k)`: m=1 {(1,3),(3,1),(5,5)}; m=2 {(0,2),(1,0),(2,4),(3,2),(4,0),(5,4)}; m=3 {(1,3),(3,3),(5,3)}; m=4 {(0,4),(1,0),(2,2),(3,4),(4,0),(5,2)}.
Note `g(D²n,h)=g(D²,nh)g(n,h)`: the dilation can sit on the block's own Gauss polynomial, evaluated at `n^jh`, with the residual untouched.

**3.5.3 Units, 2, λ, generator change, unit orbits.** Closed forms for primary `n` [N, 136-element sample; the smallest periods below are found numerically, Lean has `unitSupplement_periodic` (mod 36), `twoSupplement_periodic` (mod 8), `idealRowHom_lambda_mod_thirty_six`, `idealRowHom_two_formula`, `idealRowHom_lambda_formula`]:
`χ_n(−1)=(−1)^{(N−1)/2}` (period 4), `χ_n(ω)=ζ₆^{(N−1)/3}` (period 9), `χ_n(2)³=χ₈(N)`, `χ_n(2)²=(n mod 2)∈F₄^×≅μ₃` (period 8), `χ_n(λ)³=lambdaQuadraticTable(n mod 4)`, `χ_n(λ)` period 36.
Hence `g(n,−h)=(−1)^{(N−1)/2}g(n,h)`, `g(n,ωh)=ζ₆^{−(N−1)/3}g(n,h)` (169+169 cases): for columns with `N(n)≡1 (mod 36)` the polynomial is invariant under all six unit multiples of `h` (100 cases): six distinct points, equal values (a constant factor 6).
The baseline's `numeratorBadTwist u a b r = unitSupplement u·supportedIdealRow λ^a·twoSupplement^b·reciprocityPhaseMonoid r` is, by 3.5.1, a *single* symbol `χ_n(E_tot)` of a bounded `E_tot` (all four factors are bounded dilations).
Remark (argument only, not tested): bounded dilations can give only polylog gains as exact copies, because `χ_n(E)=1` on the whole support, for a pool of `P` non-sixth-power elements, forces density about `6^{−P}` among the alphabet primes.

**3.5.4 Conjugation.** `g(ā,h̄)=conj g(a,h)` for every supported generator `a` (`χ_{ā}(x̄)=conj χ_a(x)`, `ψ_{ā}(x̄)=conj ψ_a(x)`) [N, 131 + 20 at 40 digits; no Lean lemma]. It swaps block `D` with `D̄`, classes `E₀=λ↔−λ`, and halves case analyses.
Corollary [N, 740 symbol checks over all split primary primes of norm ≤ 400 and exponents ≤ 3, 199 Gauss-sum checks]: a prime and its conjugate multiply **without any twist or sign**: `cross(a^i,ā^j)=χ_a(ā)^{ij}χ_ā(a)^{ij}=1`, i.e. `(a/ā)₃=1`, `ε(a,ā)=1`, `g(aā,h)=g(a,h)g(ā,h)` for every `h`, and `g(aā,h)=N(a)` for integer `h` prime to `q=aā`.

**3.5.5 Block scalars (what the selected factor is).** [N unless stated]
* imprimitive reduction [L: `primePowerGauss_lift`, `sexticGauss_prime_power`]: `g(p^j,p^{j−1}h')=N^{j−1}G_j(p,h')`, `G_j(p,h)=Σ_{d mod p}χ_p(d)^jψ_p(hd)` (240 cases). Squared block = **cubic** Gauss sum, cube block = **quadratic** Gauss sum, 4th = conjugate cubic, 5th = conjugate sextic.
* Davenport–Hasse (m=2): `G₁G₄ = χ_p(2)⁻²G₂G₃` (231 cases).
* Kummer: `G₂(π,1)³ = −N(π)·π` (74/74, 20 at 40 digits); `G₃(π,1)² = χ_π(−1)N`; sixth-power law **`g(D,h)⁶ = (−1)^{(N−1)/2}·N(D)·D⁴`** for squarefree primary `D` and every `h` prime to `D` (300).
* quadratic sum explicitly: for `π=a+bω` split, `N=N(π)`: `G₃(π,1) = ((−b)/N)·ε_N·√N`, `ε_N=1 (N≡1 mod 4), i (N≡3 mod 4)` (74/74): the **cube-block scalar is elementary** (Legendre symbols), `g(π³,π²h')=N²(h'/π)₂G₃(π,1)`.
* Jacobi link: `g(D,H')² = J_D·g(D²,DH')/N` with `J_D=G₁²/G₂=ν_D·D`, `ν_D` a unit, `ν_D³=−χ_D(−1)` (all 74 primes; 40/40): the squared-block scalar is the square of the simple one up to `J_D/N`.
* inert `q` (primary generator `−q`): `g(q,h)=(−1)^{(q+1)/2}·q·χ_q(√−3·h)⁻¹` (65 cases + 5 at 40 digits): real up to the symbol of `√−3h`; `|g|=q`.

**3.5.6 Several blocks.** All identities are exponent-wise multiplicative: for `B=∏D_i^{m_i}`, `leftover = ∏ε(D_i,n)^{m_i}χ_n(D_i)^{2m_i+k_i}`, exact dilation `∏D_i^{(4m_i mod 6)}` up to `ε(B,n)`; `B=D₁D₂²`: `D₁⁴D₂²`, cost `(4w₁+2w₂)/(w₁+2w₂)`.
The frozen part `f` of a column `u=fDn` is just another block: its row shift is `χ_n(f)²ε(f,n)`, absorbable by `f⁴` (and `E₀(f)³`), or kept as a coefficient twist. (815 + 228 + 98 cases; residual equal to the conjugate prime: 96/96.)

## 4. Numerical ledger

Double precision (ratios of Gauss sums identified with an exact 6th root of unity, tolerance 1e−7; all symbol exponents are exact integers mod 6), 40 digits for the cases marked mp. Seeds are fixed in the scripts.

| script | content | cases | failures |
|---|---|---|---|
| `t0_basics.py` | Lean theorems L1–L4 (unit scale, CRT, reciprocity, fourth power) | 2787+187+586+500 | 0 |
| `e12_cross_dilation.py` | cross factor m=1..6 (500/450/350/200/60/25), 78 leftover cells, free-variable form, negative control | 1585 (×13 cells), 1560 | 0 |
| `e8_large_primes.py` | same, `N(D)` up to 1500, all 12 classes, sign-free form | 366 | 0 |
| `e34_vanishing_pools.py`, `e4_pools.py` | local vanishing table, non-coprime criterion (single and two common primes), pool grid | 143+111; 1172 + 114 (+table 84); 234+1265+95 | 0 |
| `e5_other.py` | conjugation, supplements, E₀ classes, F₄ form, multi-block, sign-free | 131; 136; 307; 144; 815+228+98 | 0 |
| `e6_gauss_structure.py`, `e9_jacobi.py` | imprimitive reduction, DH, inert, Kummer, Jacobi, cube-block closed form | 240; 231; 65; 74; 40+74 | 0 |
| `e7_wholecolumn.py` | whole column with sign, range sharpness | 614 in; 45 out (all fail as predicted) | 0 |
| `e10_misc.py`, `e11_bidilation.py` | generator change, composite pool, unit orbit, conjugate pairs, bi-dilation | 237; 207; 100; 740+199; 900×144 | 0 |
| `e13_exhaustive.py` | sign-free identity for ALL pairs of primary primes of norm ≤ 100 and blocks `D^m` (m ≤ 3) | 2046 | 0 |
| `v_final.py` | all 144 class pairs, E₀ table, sixth-power law, Kummer, inert, unit orbits | 3349; 144+144; 300; 74+74; 65; 338 | 0 |
| `highprec.py` | mpmath 40 digits: cross, dilated, sign-free, `D¹`, squared, cube, pools, Kummer, inert, conjugation | ≈ 330 | max rel. error 4e−38 |

## 5. Lean map and gaps (item 6)

| identity | proved by (file) | missing |
|---|---|---|
| unit scale | `sexticGauss_unit_scale` (Detector/CalibrationRemoval), `idealRowHom_argument_pow` (ChineseRemainder/FrequencyLifts) | – |
| CRT | `sexticGauss_coprime_product` (Detector/PhysicalCRT) | – |
| reciprocity sign | `idealRowHom_primary_reciprocity`, `sexticReciprocityPhase_mul_left/right`, `quadraticRaySign_symm/_sq` (Eisenstein/ConjugateLevelAction); `supported_opposite_phase`; `supported_phase_sq` | – |
| cross factor `p^k·u` | `crossFactor_primary`, `gauss_primary_power_product`, `residualCharacter_moving`, `gaussRow_shortening` (Moments/AmplificationShortening); `normalized_coprime_product` (Sil MixedSelectedCommon) | composite-block iteration: induction on the number of prime factors |
| T1 simple block | `fourth_power`, `normalized_fourth_power`, `whole_column`, `fifth_free_nonunit_zero`, `prime_power_nonunit_zero` (Sil GaussTransfer); `selected_row_fourth` | – |
| general `D^s`, local `FifthFree` | proof pattern of `prime_power_nonunit_zero` (`primePowerGauss_nonprincipal_extra_divisibility`) | state `sexticGauss a (D^s k)=χ_a(D)^{[−s]}sexticGauss a k` and the vanishing for `v_p(a)≤s·v_p(D)`, `6∤v_p(a)` |
| T2 squared block | `square_twist`, `square_gauss` (arvi_mixed_step/Collision/SquareGauss, H'-form); `supported_sq` | h-form `g(d²a,h)=g(d²,h)g(a,d²h)`: `normalized_coprime_product` with `d²`, `ε(d²,a)=1`, unit scale, `supported_sixth_value` |
| T3/T4/T5/T6 | same ingredients plus `idealRowHom_sixth_eq_mask`, `supported_sixth_value`, `gauss_prime_power_six` | glue lemmas; T5/T6 are outside `FifthFree`/`PowerFree 5` |
| pool | `gauss_sixth_frequency` (Moments/Amplification), `sexticGauss_pool_prime_mask`, `gaussRow_pool_prime_mask` (Collet GaussMask, hypothesis `¬p²∣a`) | extension to `v_p(a)≤5`: `fifth_free_nonunit_zero` with `D=p`, `k=p²h` covers ≤4, `gauss_prime_power_six` the case 5 |
| valuation selector | `actualSextic_primePowerGauss_at_pow` (Detector/Sextic), `primePowerGauss_at_pow_nonprincipal/principal`, `sexticGauss_prime_power`, `gauss_prime_power_one/six` | packaged theorem (CRT + local table) |
| imprimitive reduction | `primePowerGauss_lift`, `sexticGauss_prime_power` | – |
| sign as dilation (C, W) | `lambdaQuadraticTable`, `lambdaQuadraticTable_mul`, `idealRowHom_lambda_cube/_formula` (RowCompletion/ThetaNonvanishing), `unitSupplement`, `unitSupplement_periodic` (CubicReopening), `quadraticRaySign`, `firstPhaseTable` | `(−1/n)₂` as a function of `n mod 4`; decidable 12×12 lemma `quadraticRaySign r s = q_{E₀(r)}(s)`; glue `sexticReciprocityPhase d a = idealRowHom (E₀ (residue d)) (span a)^3` |
| supplements | `idealRowHom_two_formula`, `twoSupplement`, `idealRowHom_lambda_formula`, `numeratorBadTwist` | closed forms of `χ_n(−1)`, `χ_n(ω)` in `N(n)` |
| bi-dilation, multi-block | unit scale + CRT + `crossFactor_primary` | glue |
| conjugation | – (only `conjO`, `canonicalSextic_conj_as_row_label` pieces) | `sexticGauss (conjO a) (conjO h) = star (sexticGauss a h)` needs `conjO`-equivariance of `quotientTrace` and `actualSextic` |
| DH, Kummer, inert, Jacobi, cube-block closed form | – (not in the baseline files read) | classical; not needed for the descent |

## 6. What changes for the project (algebra only; pricing is R2's)

* The transfer is a one-parameter family indexed by the block multiplicity: exact residual dilation `D^{4m mod 6}`; `m=2` is exact with cost 1 per selected unit (against 4), `m=3,6` need none, `m=5` has cost 2/5. The "4 is optimal" statement is a statement about `m=1`.
* The prices are not free: block `D^m` needs `D^{m−1}∥h` (support density `N^{−(m−1)}`), has a spike of height `N^{(m−1)/2}` (mean square unchanged), and per frequency only the primes `D` with `D^{m−1}∥h` can be selected; columns must contain `D^m` exactly (`D∤n`), and residual columns must satisfy the range of §3.3.
* The ray sign is not a quadratic character of the selected modulus; it is a mod-4 object and can be removed exactly: restrict `D≡ζ (mod 4)` (density 1/4), or dilate by `E₀³` (norm ≤ 27).
* Twist type ↔ sieve: leftover `Q` is the kernel of the quadratic sieve already in the library (`quadraticRow`), `C` of the cubic sieve (`idealKernel`), `S` only meets the generic sextic sieve (Sil `FourthPower/SexticSieve`, not read here); the table of §3.2 says which `(m,k)` land where (e.g. `m=1,k=1: Q`; `m=1,k=2: C`; `m=4,k=1: Q`; `m=2,k=5: Q`; `m=3,k=3: Q`).
* Corrections to the working notes: (1) twist is `ε·χ_n(B)²`, not `χ_n(B)²`; (2) leftover of `D¹` is `(n/D)₂`; (3) `g(D²,h)≠0` iff `D∥h`, not `D|h`; (4) the pool mask holds for `v_p(u)≤5`; (5) `FifthFree` is only needed at one common prime of `D` and the column; (6) "4 is the least exponent" only for simple blocks.

## Appendix A. Lean-ready statements for the glue (not written, not compiled)

    -- general dilation (U + argument_pow)
    sexticGauss a _ (D^s * k) = (idealRowHom D (span {a}))⁻¹ ^ s * sexticGauss a _ k              -- IsCoprime D a
    -- every block, unreduced exponent (crossFactor_primary / normalized_coprime_product + unit scale)
    sexticGauss (d^m * a) _ k = sexticReciprocityPhase d a ^ m * sexticGauss (d^m) _ k * sexticGauss a _ (d^(4*m) * k)
    -- ray sign as a quadratic symbol of a bounded element (finite decide on Coord x Coord + idealRowHom_lambda_cube)
    def E0 : Coord → O          -- 1 on {(1,0),(0,1),(3,3)}, -1 on {(3,0),(0,3),(1,1)}, λ on {(3,1),(3,2),(2,1)}, -λ on {(1,3),(1,2),(2,3)}
    sexticReciprocityPhase d a = (idealRowHom (E0 (residue d)) (span {a}))^3                      -- d, a primary, supported
    -- sign-free block factorisation (m arbitrary; E0 taken at the class of d^m)
    sexticGauss (d^m * a) _ k = sexticGauss (d^m) _ k * sexticGauss a _ ((E0 (residue (d^m)))^3 * d^(4*m) * k)
    -- local vanishing (generalises prime_power_nonunit_zero / fifth_free_nonunit_zero; D with multiplicities v_p(D))
    (∃ p prime, p ∣ a ∧ p ∣ D ∧ multiplicity p a ≤ s * multiplicity p D ∧ ¬ 6 ∣ multiplicity p a) → sexticGauss a _ (D^s * k) = 0
    -- pool mask for sixth-power-free columns (generalises sexticGauss_pool_prime_mask)
    ¬ p^6 ∣ a → sexticGauss a _ (p^6 * h) = if p ∣ a then 0 else sexticGauss a _ h
    -- valuation selector (1 ≤ i ≤ 5, p ∤ h, p ∤ u')
    sexticGauss (p^i * u') _ (p^k * h) = 0 unless k + 1 = i ;  at k + 1 = i: = ε(p,u')^i * χ_{u'}(p)^(i+1) * g(p^i, p^k h) * g(u', h)
