// Create a compact record after running the standard checker on a local worker.
import { readFileSync, writeFileSync } from "node:fs";
import { parseArgs } from "node:util";
import { verificationResult } from "./actions/result.mjs";
import { workerCertificate } from "./certificate.mjs";
const { values: v } = parseArgs({
  options: Object.fromEntries(
    ["context", "attempt", "report", "report-url", "out"].map((k) => [
      k,
      { type: "string" },
    ]),
  ),
});
if (Object.values(v).length !== 5)
  throw Error("Required: --context --attempt --report --report-url --out");
const { expected } = JSON.parse(readFileSync(v.context, "utf8"));
const attempt = JSON.parse(readFileSync(v.attempt, "utf8"));
const report = verificationResult(
  process.cwd(),
  expected,
  attempt,
  "success",
  () => {
    throw Error("A completed local proof check is required");
  },
);
const record = workerCertificate(
  expected,
  report,
  v["report-url"],
  readFileSync(v.report),
);
writeFileSync(
  v.out,
  JSON.stringify({ ...record, ...expected }, null, 2) + "\n",
);
