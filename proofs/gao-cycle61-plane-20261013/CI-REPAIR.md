# Compilation repair at 0.8748598

The previous hosted attempt reached the 600-second limit while compiling `Candidate.Bundles.B167`. This revision splits B167 and B176 into smaller modules and narrows expensive tactics in B176Part2. The exact boundary `4374299/5000000` and all 43 original public declaration types are unchanged.

All 14 changed or added modules pass individual local compilation checks. The slowest takes 570.451 seconds; hosted timing still needs validation. The full revised source contains 206 modules. Its complete replay and independent Comparator/three-kernel verification are pending.

The prior 194-module source passed full local verification. Its source pin and summary are preserved in [the historical summary](local-verification/r6-verification-summary.json) and [historical source pin](local-verification/r6-source-pin.json). Those completed receipts apply to the prior source, not this revision. The [current summary](verification-summary.json) and [current source pin](source-pin.json) describe this revision. The mathematical note and exact parameter certificates are unchanged. The note’s 194-module verification paragraph records the prior R6 checks; it does not claim verification of the revised source.
