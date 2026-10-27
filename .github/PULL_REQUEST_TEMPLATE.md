QRH-Result: stable-result-id
QRH-Bound: exact-bound
QRH-Decimal: decimal-approximation

<!-- Save the metadata below as submissions/<result-id>/metadata.json.
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

- [ ] I understand that my proof and its required source dependencies must build
      and pass Comparator, Lean, NanoDa, and con-ron within **12 hours** on one
      **6-vCPU x86-64 Linux worker with 24 GiB total RAM and an 80 GiB disk**.
      I have read the [admission resource limits](https://github.com/GTimG/QuasiRiemannTracker/blob/main/README.md#admission-resource-limits),
      including the lower sandbox memory limits and individual phase deadlines.

<!-- This requirement applies to proof submissions and changes to proofs.
Maintenance-only PRs can omit this checklist and use a plain description. -->
