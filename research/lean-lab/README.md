# Lean lab

Small Lean 4 files proved (or disproved) during research. Each file states which research note it
belongs to and whether the lemma was useful. They are not part of the submission build.

Build one file against the submission's Mathlib:

```sh
cp FILE.lean /home/user/lean-env/qrh/Scratch/Lab/
cd /home/user/lean-env/qrh && PATH=/home/user/lean-env/lean-4.34.1-linux/bin:$PATH \
  lake env lean Scratch/Lab/FILE.lean
```

| file | content | status | used? |
|---|---|---|---|
| `LemmaF.lean` | Cap induction (Lemma F): with the node as its own LOW parent the crossing excess equals the mesh, the amplifier is `a' = (qe+r)/(1-6qB/Λ)`, the residual gain is exactly `r`, and the weak guard is `b - c ≤ 6a(B/Λ - c) + e` | proved | gain 3.2e-6, below the bar (`../cap-induction`) |
| `MIBranches.lean` | The marked inverse moment's binding child: the column branch is exactly `r + 2z ≤ m`; the row branch equals `F_c/2` at `v = 0` and `F_c - 3z/2` at `v = H`, so it never binds | proved | barrier: explains why slot cost 2 cannot be lowered from the row side |
| `CoupledHybrid.lean` | Abstract duality step of the coupled hybrid norm (cubic-symbol coupling between slot groups removes the `L` term of MF2.29) | proved | improves only the row branch, hence no θ gain (see `MIBranches.lean`) |
| `ReturnAlgebra.lean` | FR13's `13h/75`, `−9d/100` are `(z₀ − 1/6)h`, `(1/4 − z₀)d` with `z₀ = 17/50`, so `z₀` cancels at `d = h`; the unmarked three-line balance gives `ρ(ν) = 1 − 10ν/(15 − 6ν)`; with the gain at its cap `νb` the HIGH gate is exactly `t ≤ 10/(15 − 6ν)` | proved | barrier: locates the binding inputs (`../chain-ode`, `../LOG.md`) |
| `RotatedSelfParent.lean` | A Lemma F self step is an ordinary source step with a rotated parent: child `(B₀ − ηc, Λ₀ − η, c')` has crossing exactly `c`, Collet's budget holds with equality, the LOW excess is `(η(b − c) + Λe)/Λ₀`, and the child's line crosses the parent's at `c` | proved | formalization route for Lemma F with the existing predicates (`../cap-induction/README.md` §5) |
| `MaximalEnvelope.lean` | Comparison principle for the continuum face map: if the minimal admissible slope `Λ(s, e)` is nondecreasing in the height `e`, every envelope with `E' ≤ −Λ(s, E)` stays below the solution of `Ê' = −Λ(s, Ê)` from the same start (core: a function that is nonincreasing wherever it is positive and starts `≤ 0` stays `≤ 0`) | proved | the continuum solution is the ceiling of its class (`../variational-ceiling/`) |
