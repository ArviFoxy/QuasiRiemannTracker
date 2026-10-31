# Fresh look 3 (2026-10-31): θ overall, ≥ 5e-5 within reach?

A delegated review with a neutral brief: the whole problem, our lever map quarantined as "challenge it", and pricing
with the float models. All scripts are float models built on the repo's own models
(`../second/base_models/worth.py` and `../../selected-leaf/{root_ledger,ledger_gamma2,envelope_c}.py`). They run in
place: `python3 <script>`. Summary and evaluation: `../../journal/JOURNAL.md`, entry "Fresh look 3".

| script | what it does |
|---|---|
| `m0.py`, `m1.py` | binding landscape over (δ, p); global grid check; the region within 2.35e-4 of the binding (a flat ridge δ ∈ [0.386, 0.464], p ∈ [0.485, 0.5]) |
| `m2.py` | θ* with the count face and the physical face separated (worth.py logic) |
| `m3.py` | continuum marked density chain past the native end, used as a count face: dead (≤ 1.2e-5) |
| `m4.py`–`m9.py` | prices of count-only and both faces along K < 1/2 lines; read-point slot widths at the binding (count ≈ 0.13, physical ≈ 0.071) |
| `m10.py`–`m12.py` | the width-floored count face (faces below Λ = 2 claimed only for slot widths ≥ s0) and the jump guard from Collet's window; output `m12_out.txt` |
| `kwlib.py` | K-wall ledger: native line from the banked K = 1/2 end face with the prime-dilated principal gate; faces claimed only for S ≥ s0 (base-face fallback below the floor); selected-norm excess uniform or geometry-resolved |
| `kw.py`, `kw2.py`–`kw5.py` | uniform-γ tolerance with a width floor |
| `kw6.py`–`kw9.py` | geometry-resolved excess (per-twist-range bounds, under C); output `kw9_floor.txt` |
| `kw10.py`, `kw11.py` | tolerated uniform γ for the floored line (≈ 0.048 at K = 0.45, s0 = 0.118, stop 1.90); output `kw10_out.txt` |
| `kw12.py`, `kw13.py` | the same with the proven `OptimalBound` majorant (theta terms kept) plus the pointwise cubic bound; still ≈ B^{0.14} short; outputs `kw12_out.txt`, `kw13_out.txt` |

Caveats (the review's own): float prices are ceilings (the exact all-edge check, `../../frontier/conditional_exact.py`,
shows the float overstating below Λ ≈ 1.95); the jump guard is the review's reading of Collet's `AdmittedWindow`,
not yet checked exactly; the ledger is the simplified model of Sil's step; C at its fixed point is assumed.
