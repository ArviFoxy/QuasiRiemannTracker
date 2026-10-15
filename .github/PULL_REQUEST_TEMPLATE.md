QRH-Result: stable-result-id
QRH-Bound: exact-bound
QRH-Decimal: decimal-approximation

<!-- For maintenance, replace this template with a description of the change.
For a result, start from current main and commit both required files:
  submissions/<result-id>/metadata.json
  submissions/<result-id>/src/Candidate/Main.lean (theorem Candidate.bound)
Use the same result ID in the directory name and QRH-Result above.

Admission reads publication metadata from the committed metadata.json at the
exact PR head. Example file contents for a proof importing the OpenAI baseline:
{
  "title": "Result title",
  "authors": [{"name": "Your name"}],
  "description": "Method and attribution to previous work.",
  "dependencies": ["openai-baseline"]
}
Required fields: title, authors, description. Declare directly imported
submission directory names in dependencies. Optional fields: license, builds_on
(existing result IDs for attribution), references (objects with label and HTTPS
url). Author objects also accept an HTTPS url. See README.md#submit for details.

Give an exact reduced fraction or supported exact algebraic expression. Give an
accurate truncated decimal with enough digits to differ from the current best
verified bound. Equal bounds accept any supported decimal precision.
Actions checks the exact PR head, including drafts. After merge, deployment
builds the website catalogue from the submission and its verification record. -->
