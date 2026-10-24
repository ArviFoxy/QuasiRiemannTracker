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
