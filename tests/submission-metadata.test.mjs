import test from "node:test";
import assert from "node:assert/strict";
import {
  parseSubmissionMetadata,
  validateSubmissionMetadata,
} from "../verifier/submission-metadata.mjs";

const metadata = () => ({
  title: "A candidate bound",
  authors: [{ name: "Example researcher", url: "https://example.org/author" }],
  description: "The argument improves a moment estimate.",
});
const block = (value) => "```qrh-metadata\n" + JSON.stringify(value) + "\n```";

test("the PR JSON supplies publication metadata once, with optional credits", () => {
  const value = {
    ...metadata(),
    license: "Apache-2.0",
    builds_on: ["earlier-result"],
    references: [{ label: "Paper", url: "https://example.org/paper" }],
  };
  assert.deepEqual(
    parseSubmissionMetadata("QRH-Result: candidate-proof\n\n" + block(value)),
    value,
  );
});
test("missing, ambiguous, and malformed publication metadata cannot be admitted", () => {
  for (const body of [
    "",
    "A description without metadata",
    block(metadata()) + "\n" + block(metadata()),
    "```qrh-metadata\n{bad json}\n```",
  ])
    assert.throws(() => parseSubmissionMetadata(body), /metadata|JSON/);
});
test("publication metadata cannot provide verification claims or unsafe links", () => {
  for (const changes of [
    { status: "framework-verified" },
    { theta_exact: "1/2" },
    { title: "" },
    { authors: [] },
    { authors: [{ name: "Example", url: "javascript:alert(1)" }] },
    {
      references: [
        { label: "Paper", url: "https://user:password@example.org" },
      ],
    },
    { builds_on: ["../other-proof"] },
    { builds_on: ["earlier-result", "earlier-result"] },
  ])
    assert.throws(
      () => validateSubmissionMetadata({ ...metadata(), ...changes }),
      /Invalid publication metadata/,
    );
});
