# Agent traces

Agent traces are recommended and optional. They help others understand how a
proof was developed, including approaches that did not work. Missing traces do
not block a submission; supplied traces must pass the checks below.

## Where to put them

Match the corresponding submission directory exactly:

```text
submissions/2026-10-28-example-bound/metadata.json
submissions/2026-10-28-example-bound/src/Candidate/Main.lean
agent-traces/2026-10-28-example-bound/run-01.json
agent-traces/2026-10-28-example-bound/run-02.jsonl
```

Link the trace files in your PR. Keep the submission's original date and directory
name when adding or correcting traces later. Traces live outside the proof
directory, so a trace-only maintenance PR does not trigger another Lean
verification.

## Format

Prefer [ATIF (Agent Trajectory Interchange Format)](https://docs.harborframework.com/agents/atif).
Native exports are also accepted: a `.json` file must contain an object or array;
each nonblank line of a `.jsonl` file must contain an object. No conversion to
ATIF is required. Use UTF-8 text, with at most **10 MiB per file**, **50 MiB per
submission**, and **50 trace files per submission**. Split longer sessions into
numbered files within those limits.

Preserve the available agent and model names and versions, original prompts,
messages, tool calls, outputs, and failed attempts. Timestamps and usage metrics
are useful when available. Export the recorded interactions; do not invent
missing history. For ATIF, describe redactions or omissions in an `extra` field.

This illustrative ATIF-v1.7 example shows the structure; replace it with your
actual exported history:

```json
{
  "schema_version": "ATIF-v1.7",
  "agent": {
    "name": "my-agent",
    "version": "1.0.0",
    "model_name": "model-used"
  },
  "steps": [
    {
      "step_id": 1,
      "source": "user",
      "message": "Improve the bound and verify the Lean proof."
    },
    {
      "step_id": 2,
      "source": "agent",
      "message": "Checking the candidate proof.",
      "tool_calls": [
        {
          "tool_call_id": "call-1",
          "function_name": "shell",
          "arguments": { "command": "lake build" }
        }
      ],
      "observation": {
        "results": [
          {
            "source_call_id": "call-1",
            "content": "Build completed successfully."
          }
        ]
      }
    }
  ]
}
```

Repository checks validate JSON structure, paths, and size limits, rather than
enforcing the complete ATIF schema. Referenced external assets are not fetched.

## Check before uploading

Remove API keys, tokens, passwords, and private information before committing.
Install [Gitleaks v8.30.1](https://github.com/gitleaks/gitleaks/releases/tag/v8.30.1)
on your `PATH`, then run from the repository root:

```sh
node scripts/check-agent-traces.mjs agent-traces/2026-10-28-example-bound
```

Omit the path to check all submitted traces. The same checks run on the exact PR
commit on a GitHub-hosted runner before proof verification. Gitleaks scans the raw
files and decoded JSON strings for suspected credentials; findings are redacted
in check output. The check does not try credentials against external services.

Scanning is a basic safeguard and cannot guarantee that a trace contains no
secrets. CI runs after upload: check locally first, and revoke any real
credential accidentally pushed, even if you subsequently remove it.
