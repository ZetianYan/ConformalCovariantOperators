import fs from "node:fs";
import path from "node:path";

const root = path.resolve(import.meta.dirname, "..");
const sourceRoot = path.join(root, "public", "source");
const notesRoot = path.join(root, "public", "module-notes");
const allowedStatuses = new Set(["verified", "verified-under-interface", "scaffold", "planned", "needs-review"]);
const walk = (dir) => fs.readdirSync(dir, { withFileTypes: true }).flatMap((entry) => entry.isDirectory() ? walk(path.join(dir, entry.name)) : [path.join(dir, entry.name)]);
const rel = (base, file) => path.relative(base, file).split(path.sep).join("/");
const sources = walk(sourceRoot).filter((f) => f.endsWith(".lean")).map((f) => rel(sourceRoot, f)).sort();
const notes = walk(notesRoot).filter((f) => f.endsWith(".json") && !f.endsWith("module-index.json")).map((f) => rel(notesRoot, f).replace(/\.json$/, ".lean")).sort();
const references = JSON.parse(fs.readFileSync(path.join(root, "public", "references.json"), "utf8"));
const referenceIds = new Set(references.map((x) => x.id));
const errors = [];
let translationCount = 0;
const placeholderPattern = /exact mathematical type|formal proposition:|data\/interface:|preserved from the lean signature/i;

for (const file of sources.filter((x) => !notes.includes(x))) errors.push(`Missing note: ${file}`);
for (const file of notes.filter((x) => !sources.includes(x))) errors.push(`Orphan note: ${file}`);
for (const file of sources) {
  const noteFile = path.join(notesRoot, file.replace(/\.lean$/, ".json"));
  if (!fs.existsSync(noteFile)) continue;
  const note = JSON.parse(fs.readFileSync(noteFile, "utf8"));
  const source = fs.readFileSync(path.join(sourceRoot, file), "utf8");
  const lineCount = source.split(/\r?\n/).length;
  for (const field of ["file", "title", "status", "summary", "mathematicalContent", "correspondence", "prerequisites", "usedBy", "references", "limitations"]) {
    if (note[field] === undefined || note[field] === null || note[field] === "") errors.push(`${file}: missing ${field}`);
  }
  if (note.file !== file) errors.push(`${file}: file field mismatch`);
  if (!allowedStatuses.has(note.status)) errors.push(`${file}: invalid status ${note.status}`);
  for (const ref of note.references ?? []) if (!referenceIds.has(ref.referenceId)) errors.push(`${file}: unknown reference ${ref.referenceId}`);
  // Ignore Lean comments before counting declarations. Without this, prose such
  // as "a later theorem can ..." inside a module doc comment is misclassified.
  const sourceWithoutComments = source
    .replace(/\/-[\s\S]*?-\//g, (comment) => comment.replace(/[^\r\n]/g, " "))
    .replace(/--.*$/gm, "");
  const sourceDeclarationCount = [...sourceWithoutComments.matchAll(/^\s*(?:noncomputable\s+)?(?:structure|class|def|abbrev|inductive|theorem|lemma|axiom)\s+([^\s(:{]+)/gm)].length;
  if ((note.correspondence ?? []).length !== sourceDeclarationCount) errors.push(`${file}: translated ${(note.correspondence ?? []).length} of ${sourceDeclarationCount} top-level declarations`);
  for (const item of note.correspondence ?? []) {
    translationCount++;
    if (!Number.isInteger(item.line) || item.line < 1 || item.line > lineCount) errors.push(`${file}: invalid line for ${item.leanDeclaration}`);
    if (!source.includes(item.leanDeclaration)) errors.push(`${file}: declaration not found: ${item.leanDeclaration}`);
    if (!item.mathematicalMeaning?.trim()) errors.push(`${file}: missing mathematical translation for ${item.leanDeclaration}`);
    if (!item.mathematicalFormula?.trim()) errors.push(`${file}: missing mathematical formula for ${item.leanDeclaration}`);
    if (!item.leanType?.trim()) errors.push(`${file}: missing Lean signature for ${item.leanDeclaration}`);
    if (placeholderPattern.test(item.mathematicalMeaning ?? "")) errors.push(`${file}: placeholder explanation remains for ${item.leanDeclaration}`);
  }
}
const index = JSON.parse(fs.readFileSync(path.join(notesRoot, "module-index.json"), "utf8"));
if (index.length !== sources.length) errors.push(`module-index has ${index.length} entries; expected ${sources.length}`);
if (errors.length) {
  console.error(errors.join("\n"));
  process.exit(1);
}
console.log(`Validated ${sources.length} module notes, ${translationCount} declaration translations, and ${references.length} references.`);
