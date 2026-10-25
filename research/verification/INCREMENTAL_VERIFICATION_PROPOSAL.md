# Draft: incremental kernel verification for PR admission (for the maintainers; not posted)

**Problem.** Since about PR #63 no admission has passed the hosted check. The hosted runner (4 vCPU,
16 GB) gets one kernel job, so Comparator, nanoda and con-ron run in sequence under a one-hour
judge budget, inside a three-hour shared deadline with a 600 s export limit. Every result from
#63 to #71 was therefore re-verified offline on a 16-thread / 192 GiB worker with budgets raised to
6–12 h, and a hosted run on `main` fails the same way.

**Why.** Most of each candidate's closure is already verified. For PR #73 (measured on a 4-core /
15 GB machine), by export bytes:

| part | share of the 4.3 GB export |
|---|---|
| admitted dependency (hailey-collet-1252270103) | 54% |
| openai-baseline | 19% |
| Mathlib | 19% |
| new declarations | 7% |

The export alone takes 511 s with a 12.3 GB peak, which is already at the hosted limits.

**Proposal: check only the delta, keyed by hashes of the already-verified declarations.**
1. When a result is admitted, store a manifest of its verified closure: declaration name, the hash
   of its exported type and value, and its axioms. All three kernels must accept it, as today.
2. For a new candidate, export as today. Every declaration whose name and hash match an admitted
   manifest is treated as an axiom-like trusted constant when the kernels replay; only the new
   declarations are checked.
   - nanoda and con-ron would need a way to accept a trusted prefix (or a pre-checked environment
     snapshot).
   - The Lean default replay can start from the admitted environment.
3. Comparator's statement and axiom comparison is unchanged and still covers the full transitive
   closure, so soundness rests only on the hash match.

**Effect.** For #73 the kernels would check about 7% of the bytes, minutes instead of hours on the
hosted runner. The export cost could be cut the same way, by exporting only declarations outside
the admitted manifests.

**Alternatives.**
- Larger hosted runners (3 kernel jobs in parallel).
- Keep the current offline process, and document it as the expected path for large closures.
