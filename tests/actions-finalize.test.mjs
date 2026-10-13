import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
const repository = "GTimG/QuasiRiemannTracker",
  head = "a".repeat(40);
const entrypoint = new URL("../verifier/actions/finalize.mjs", import.meta.url)
  .href;
function fixture() {
  const expected = {
    repository,
    number: 15,
    head_sha: head,
    result_id: "candidate-proof",
    theta_exact: "1/1",
  };
  const pr = {
    state: "open",
    head: { sha: head },
    base: { sha: "b".repeat(40), ref: "main", repo: { full_name: repository } },
    body: "QRH-Result: candidate-proof\nQRH-Bound: 1/1\nQRH-Decimal: 1.0",
    changed_files: 1,
  };
  return {
    context: {
      expected,
      pr,
      repository,
      defaultBranch: "main",
      run_id: "123",
      run_attempt: "1",
      workflow_sha: "c".repeat(40),
      check_id: 456,
    },
    current: structuredClone(pr),
    attempt: {
      ...expected,
      status: "accepted",
      report: {
        status: "PASS",
        reviewed_pr_head: head,
        source_repository: repository,
        result_id: expected.result_id,
        theta_exact: "1/1",
        judge_exit_code: 0,
        targets: ["QRH.canonical_bound"],
        kernels: ["Lean default", "nanoda", "con-ron"],
        allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
        sandbox_preflight: "PASS",
        candidate_mount_preflight: "PASS",
        challenge_exported_before_candidate_execution: true,
        receipt_outside_candidate: true,
      },
    },
  };
}
function run(t, data, env = {}) {
  const cwd = mkdtempSync(join(tmpdir(), "qrh-finalize-"));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  for (const dir of ["verification-context", "verification", "catalogue"])
    mkdirSync(join(cwd, dir));
  writeFileSync(
    join(cwd, "verification-context/context.json"),
    JSON.stringify(data.context),
  );
  if (data.attempt)
    writeFileSync(
      join(cwd, "verification/attempt.json"),
      JSON.stringify(data.attempt),
    );
  writeFileSync(
    join(cwd, "catalogue/results.json"),
    JSON.stringify({
      records: [
        {
          id: "previous-bound",
          status: "framework-verified",
          theta: { numerator: "7", denominator: "8" },
        },
      ],
    }),
  );
  const script = `
 const requests=[];globalThis.fetch=async(url,options={})=>{
 const request={url:String(url),method:options.method??"GET",body:options.body?JSON.parse(options.body):undefined};requests.push(request);
 if(request.method==="GET" && request.url==="https://api.github.com/repos/${repository}/pulls/15")return {ok:true,status:200,json:async()=>JSON.parse(process.env.CURRENT_PR)};
 if(request.method==="PATCH" && request.url==="https://api.github.com/repos/${repository}/check-runs/456")return {ok:true,status:200};
 throw Error("Unexpected request");};
 let error;try{await import(${JSON.stringify(entrypoint)});}catch(e){error=e.message;process.exitCode=1;}
 console.log("RESULT="+JSON.stringify({requests,error}));`;
  const child = spawnSync(
    process.execPath,
    ["--input-type=module", "--eval", script],
    {
      cwd,
      encoding: "utf8",
      timeout: 10000,
      env: {
        GITHUB_REPOSITORY: repository,
        GITHUB_RUN_ID: "123",
        GITHUB_RUN_ATTEMPT: "1",
        GITHUB_WORKFLOW_SHA: "c".repeat(40),
        GITHUB_REF: "refs/heads/main",
        QRH_VERIFICATION_RESULT: "success",
        GITHUB_TOKEN: "test-token",
        CURRENT_PR: JSON.stringify(data.current),
        ...env,
      },
    },
  );
  assert.ifError(child.error);
  const line = child.stdout.split("\n").find((l) => l.startsWith("RESULT="));
  assert.ok(line, child.stderr);
  return { ...JSON.parse(line.slice(7)), status: child.status };
}
test("publisher accepts current-run proof without reading local receipts", (t) => {
  const result = run(t, fixture());
  assert.equal(result.status, 0);
  const published = result.requests.at(-1).body;
  assert.equal(published.conclusion, "success");
  assert.match(
    published.output.summary,
    /Proof verification accepts candidate-proof at 1\/1/,
  );
});
for (const field of ["head", "body", "base"])
  test(`publisher rejects stale ${field}`, (t) => {
    const data = fixture();
    if (field === "body") data.current.body += "\nchanged";
    else data.current[field].sha = "d".repeat(40);
    const result = run(t, data);
    assert.equal(result.status, 1);
    assert.equal(result.requests.at(-1).body.conclusion, "failure");
    assert.match(
      result.requests.at(-1).body.output.summary,
      /changed during verification/,
    );
  });
for (const field of ["run_id", "run_attempt", "workflow_sha"])
  test(`publisher refuses artifacts from another ${field}`, (t) => {
    const data = fixture();
    data.context[field] = "other";
    const result = run(t, data);
    assert.equal(result.status, 1);
    assert.equal(result.requests.length, 0);
    assert.match(result.error, /protected workflow run/);
  });
test("publisher fails a missing result artifact", (t) => {
  const data = fixture();
  delete data.attempt;
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.match(result.requests.at(-1).body.output.summary, /report is missing/);
});
test("publisher checks decimal accuracy after successful proof verification", (t) => {
  const data = fixture();
  data.context.pr.body = data.current.body = data.current.body.replace(
    "1.0",
    "1.1",
  );
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.match(result.requests.at(-1).body.output.summary, /decimal|Decimal/);
});
