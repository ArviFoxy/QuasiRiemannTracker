// Publication metadata is authored once, in the submitted PR body. Admission
// preserves this exact data beside the checked proof and its certificate.
const text = (value, limit) =>
  typeof value === "string" && value.trim().length > 0 && value.length <= limit;
const url = (value) => {
  try {
    const parsed = new URL(value);
    return parsed.protocol === "https:" && !parsed.username && !parsed.password;
  } catch {
    return false;
  }
};
export function validateSubmissionMetadata(value) {
  const fields = new Set([
    "title",
    "authors",
    "description",
    "license",
    "builds_on",
    "references",
  ]);
  if (
    !value ||
    typeof value !== "object" ||
    Array.isArray(value) ||
    Object.keys(value).some((key) => !fields.has(key)) ||
    !text(value.title, 240) ||
    !text(value.description, 10000) ||
    !Array.isArray(value.authors) ||
    !value.authors.length ||
    value.authors.length > 100 ||
    value.authors.some(
      (author) =>
        !author ||
        typeof author !== "object" ||
        Array.isArray(author) ||
        Object.keys(author).some((key) => !["name", "url"].includes(key)) ||
        !text(author.name, 240) ||
        (author.url !== undefined && !url(author.url)),
    ) ||
    (value.license !== undefined && !text(value.license, 1000)) ||
    (value.builds_on !== undefined &&
      (!Array.isArray(value.builds_on) ||
        value.builds_on.length > 100 ||
        new Set(value.builds_on).size !== value.builds_on.length ||
        value.builds_on.some((id) => !/^[a-z][a-z0-9-]{2,63}$/.test(id)))) ||
    (value.references !== undefined &&
      (!Array.isArray(value.references) ||
        value.references.length > 100 ||
        value.references.some(
          (reference) =>
            !reference ||
            typeof reference !== "object" ||
            Array.isArray(reference) ||
            Object.keys(reference).some(
              (key) => !["label", "url"].includes(key),
            ) ||
            !text(reference.label, 240) ||
            !url(reference.url),
        )))
  )
    throw Error(
      "Invalid publication metadata: provide title, authors and description in qrh-metadata JSON",
    );
  return value;
}

export function parseSubmissionMetadata(body) {
  const blocks = [
    ...(body ?? "").matchAll(
      /^```qrh-metadata[ \t]*\r?\n([\s\S]*?)^```[ \t]*$/gm,
    ),
  ];
  if (blocks.length !== 1)
    throw Error(
      "New bounds require exactly one fenced qrh-metadata JSON block in the PR body",
    );
  let value;
  try {
    value = JSON.parse(blocks[0][1]);
  } catch {
    throw Error("The qrh-metadata block must contain valid JSON");
  }
  return validateSubmissionMetadata(value);
}
