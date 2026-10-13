# Reproduce the submitted bundles

Run `python3 verify_packaging.py` from this directory in the result checkout. To inspect a separate copy, pass `--candidate /path/to/submissions/cycle61-c0125139`.

The check reads the original source archive without extracting it, verifies every original module against the source manifest, and reconstructs each bundle from its recorded imports, module order, anonymous sections and counted repairs. It compares the reconstructed bytes with the submitted files, including the complete package inventory and tracker size limits.

`bundle_generator.py` is the unchanged generator used during packaging. The published check uses its header and repair functions with the frozen transformation map. The generator's original command-line interface describes the private development layout; readers do not need that layout to run this check. Historical rehearsal labels in the generated comments are retained to preserve the exact compiled source bytes.

The adjustments qualify names made ambiguous by combined imports and separate comparison or function-arrow tokens from notation introduced by those imports. One theorem, `actual_main_low_all_height_splice`, has a local elaboration heartbeat allowance of 40,000 instead of 20,000 in the bundled copy. Its statement and proof body are unchanged; the tracker's 600-second module and 7,200-second replay limits are unchanged. The unbundled originals remain unchanged. Each adjustment is bound to an exact original source hash and occurrence count in `repairs.json` and `transformation.json`.

This is a source-reconstruction check. Its success does not establish mathematical correctness. The complete transformed Lean replay, canonical-statement Comparator, independent kernels and tracker admission are documented separately in [Verification.md](../Verification.md).
