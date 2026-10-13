# Exact arithmetic evidence

Run `python3 rational-check.py` from any directory. The helper uses only the Python standard library and the fixed-hash `endpoint-receipt.json` beside it. It reconstructs the scalar margins and all 156 Bernstein coefficients, including closed-box coverage and disjoint interiors. It writes a fresh `rational-receipt.json` beside itself.

The historical endpoint and source-range receipts are retained byte-for-byte. Their relative paths describe the original research packet. `portability-receipt.json` records the two-line path relocation; arithmetic is unchanged. These checks do not establish the analytic hypotheses or replace Lean and independent kernel replay.
