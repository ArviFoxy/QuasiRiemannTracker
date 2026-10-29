QRH-Result: arvi-density
QRH-Bound: 43693617/50000000
QRH-Decimal: 0.87387234

Metadata: `submissions/2026-10-29-arvi-density/metadata.json`.

### Proof submission requirements

- [x] My submission directory is `YYYY-MM-DD-<slug>`, with the original PR creation date in UTC appearing only once. Later updates retain the same directory, result ID, and Lean namespace.
- [x] I understand that my proof and its required source dependencies must build and pass Comparator, Lean, NanoDa, and con-ron within **12 hours** on one **6-vCPU x86-64 Linux worker with 24 GiB total RAM and an 80 GiB disk**.

### Agent traces (recommended, optional)

None supplied.

### Notes

- Marked HIGH leaf in Sil's density step (repeated-mark count of PR 76), density floor 1/2, 129 exact marked steps from PR 86's boot face, five-branch return (PR 76's capC and weakC7 restored).
- Upstream submission tests (35/35) and the trace check pass locally. The local Lean build was still running when this PR was opened; I will update the PR with the result.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
