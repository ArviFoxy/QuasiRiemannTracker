QRH-Result: stable-result-id
QRH-Bound: exact-bound
QRH-Decimal: decimal-approximation

<!-- Save the metadata below as submissions/YYYY-MM-DD-<slug>/metadata.json.
Use the original PR creation date in UTC, once, at the start of the directory.
For new submissions, QRH-Result is the slug without the date prefix.
Existing submissions retain their stable result ID and original dated directory.
See https://github.com/GTimG/QuasiRiemannTracker/blob/main/README.md#submit
for result and maintenance PR instructions. -->

```json
{
  "title": "Result title",
  "authors": [{ "name": "Your name" }],
  "description": "Method and attribution to previous work.",
  "dependencies": ["openai-baseline"]
}
```

### Proof submission requirements

- [ ] My submission directory is `YYYY-MM-DD-<slug>`, with the original PR
      creation date in UTC appearing only once. Later updates retain the same
      directory, result ID, and Lean namespace.
- [ ] I understand that my proof and its required source dependencies must build
      and pass Comparator, Lean, NanoDa, and con-ron within **12 hours** on one
      **6-vCPU x86-64 Linux worker with 24 GiB total RAM and an 80 GiB disk**.
      Queue time and checking-environment setup are separate; lower sandbox memory
      limits and individual phase deadlines also apply. See the
      [runner configuration](https://github.com/GTimG/QuasiRiemannTracker/blob/main/infra/actions-runner/README.md).

<!-- This requirement applies to proof submissions and changes to proofs.
Maintenance-only PRs can omit this checklist and use a plain description. -->

### Agent traces (recommended, optional)

Trace paths or links: <!-- Leave blank if no trace is available. -->

<!-- Include sanitized ATIF JSON or native JSON/JSONL exports under
agent-traces/<submission-directory>/, keeping the submission's original date.
Preserve available prompts, messages, tool calls, results, and failed attempts.
Run the local secret check before pushing; uploaded traces must pass CI checks.
See https://github.com/GTimG/QuasiRiemannTracker/blob/main/agent-traces/README.md -->
