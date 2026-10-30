# arvi-selected-leaf: Dirichlet nonvanishing at θ = TBD (draft; numbers pending the Lean return)

## Summary

The leaf of Sil's cube-free native step is replaced by a **selected-norm leaf** (E5). On rows whose slot block
is heavy, the energy is bounded by PR 93's selected all-source large-sieve norm. The native line of faces can
then continue with B = 0.99999 below Sil's overshoot gate Λ = 2.5714B, down to Λ = 401/200. The return,
retuned to these faces, certifies θ = TBD (best merged: 0.87387234, PR 94).

## New mathematics

1. **R1, the selected root energy** (`arvi_selected_leaf/R1/`, theorem `selectedRootEnergy`).
   For every cut K ∈ [0.500001, 3/4], the energy of the rows with a heavy slot block is at most
   Z^{M + selExcess + ε}, where selExcess = (P + s + (M − P)₊/5 − M)₊. The proof:
   - splits the rows into sixth-root classes z = u·g⁶;
   - bounds each class two ways:
     - directly, by PR 93's selected norm on the row polynomial, which is ordinary in the core u;
     - reflectively, by the baseline's reflected radial engine applied to the radical row character of the
       class. Its conductor is ≲ N(u)N(g) = Z^M N(g)^{-5}, and the separated energies are again bounded by
       PR 93's norm;
   - sums the classes with ζ_K(1+η) and the interpolation min(a, b) ≤ a^{1−θ}b^θ.
2. **E5 leaf and line** (`arvi_selected_leaf/{Price,Gates,Step,Leaf,Unselected,Curve}`).
   - The leaf price is max(K·deletionNeed, selExcess) with K = 501/1000.
   - The native gates hold with Sil's nativeK replaced by K. The overshoot gate moves from 2.5714B to about
     2B, and the line runs to Λ = 401/200 (a = 1/1000).
3. **Return** (retuned). The E5 face serves both count and physical queries. The natural join and the plain
   floor of the count return are freed (sMinus = 27/1000, mMinus = 3/10).
4. **No density chain.** The final theorem does not use the 130-step density chain. The native line starts
   from PR 76's face through the ODE-shape native curve (`arvi_ode_shape`).

## Compile time

R1's core compiles in about 30 s and its plumbing in about 12 s (`lake env lean`). TBD: full build and
closure size.

## Builds on

openai-baseline, hailey-collet-1252270103, sil-density-split (PR 83), arvi-repeated-marks-on-sil-face
(PR 76), joint-detector-fine-chain (PR 93), arvi-density (PR 94).
