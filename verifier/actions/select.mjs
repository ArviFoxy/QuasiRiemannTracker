import { readFileSync, writeFileSync } from "node:fs";
const path = "verification-context/context.json";
const c = JSON.parse(readFileSync(path, "utf8"));
const expected = c.expectations.filter(
  (e) => e.result_id === process.env.QRH_RESULT_ID,
);
if (expected.length !== 1)
  throw Error("Unknown or duplicate verification target");
c.expected = expected[0];
writeFileSync(path, JSON.stringify(c) + "\n");
