import fs from "node:fs";
import path from "node:path";

const root = path.resolve(import.meta.dirname, "..");
const sourceRoot = path.join(root, "public", "source");
const notesRoot = path.join(root, "public", "module-notes");

const descriptions = {
  "Conformal/Basic.lean": "Models a conformal structure as a metric bundle with positive rescaling, together with scales and the comparison of representatives.",
  "Conformal/Density.lean": "Defines conformal densities through equivariance under positive metric rescaling and relates equivariant and scale-dependent presentations.",
  "Ambient/Ambientbasic.lean": "Builds the ambient bundle, dilation action, straight metric data, the cone inclusion at rho = 0, and the straight normal-form interface.",
  "Ambient/Ambientdensity.lean": "Defines homogeneous ambient densities and their restriction to conformal densities on the null cone.",
  "Ambient/Ambientoperator.lean": "Packages the abstract ambient operator calculus: Q, the Euler operator X, the ambient Laplacian, powers, homogeneity, and commutator laws.",
  "Ambient/Ambienttangential.lean": "Formalizes equality modulo the defining function Q and the condition that a weighted ambient operator descends to boundary data.",
  "Ambient/FG.lean": "Aggregate entry point for the Fefferman–Graham straight ambient normal-form component calculus.",
  "Ambient/FG/Index.lean": "Introduces the ambient 0, base, and infinity index types and formal normal coordinates used by component calculations.",
  "Ambient/FG/NormalForm.lean": "Encodes straight ambient metrics in normal form and their block metric components in the t, base, and rho directions.",
  "Ambient/FG/InverseMetric.lean": "Specifies inverse ambient metric components and verifies the formal block inverse identities in normal coordinates.",
  "Ambient/FG/Christoffel.lean": "Records the Christoffel-symbol components associated with the straight ambient normal form.",
  "Ambient/FG/Laplacian.lean": "Introduces the normal-form defining function Q = 2 rho t^2 and an interface for the ambient Laplacian in these coordinates.",
  "Ambient/FG/Commutators.lean": "Derives the Euler/defining-function/Laplacian identities used in the tangentiality argument, including XQ = 2Q and the Laplacian–Q commutator.",
  "Ambient/FG/CalculusInstance.lean": "Transfers the FG normal-form component identities into the abstract AlgebraicIdentities interface consumed by the operator calculus.",
  "Ambient/FG/RicciNormalForm.lean": "States symbolic Ricci-tensor components for an ambient metric in normal form.",
  "Ambient/FG/FormalJets.lean": "Represents a finite rho-jet of the tangential metric g_rho and the condition that it solves the FG Ricci equations to finite order.",
  "Ambient/FG/Recursion.lean": "Packages finite-order Ricci recursion data and the first-jet relation with the Schouten tensor.",
  "Ambient/FG/Obstruction.lean": "Defines even-dimensional obstruction-order data, an abstract obstruction tensor, and unobstructedness.",
  "Ambient/PE.lean": "Aggregate entry point for Poincaré–Einstein geometry, the ambient bridge, invariants, renormalization, and applications.",
  "Ambient/PE/Basic.lean": "Defines the formal Poincaré–Einstein space, its bulk and boundary dimensions, compactification data, and Einstein condition.",
  "Ambient/PE/DefiningFunction.lean": "Formalizes boundary defining functions, geodesic defining functions, and their normalization conditions.",
  "Ambient/PE/NormalForm.lean": "Encodes the Poincaré normal form g_+ = r^{-2}(dr^2 + h_r) at the level of abstract metric data.",
  "Ambient/PE/MetricComponents.lean": "Records the metric and inverse-metric block components of a Poincaré normal-form metric.",
  "Ambient/PE/EinsteinEquation.lean": "Packages the Einstein equation and parity/expansion certificates used by later PE constructions.",
  "Ambient/PE/AmbientBridge.lean": "States the formal cone relationship between straight ambient geometry and the associated Poincaré–Einstein metric.",
  "Ambient/PE/Invariants.lean": "Aggregate entry point for the symbolic PE invariant calculus.",
  "Ambient/PE/Invariants/RiemannianInvariant.lean": "Defines symbolic scalar/tensor Riemannian invariants with rank, conformal weight, tensor weight, and parity bookkeeping.",
  "Ambient/PE/Invariants/Straightenable.lean": "Defines invariants that admit evaluation through a chosen ambient model and proves closure operations at the interface level.",
  "Ambient/PE/Invariants/LaplacianRecursion.lean": "Formalizes the iterative ambient-Laplacian recursion corresponding to Proposition 3.7 in the PE renormalized-integral reference.",
  "Ambient/PE/Invariants/NaturalDivergence.lean": "Packages natural divergences and the cone-rule interface used to convert ambient identities into PE divergence statements.",
  "Ambient/PE/Invariants/Pfaffian.lean": "Defines Pfaffian-like symbolic invariants and the P_l_n family used in the Gauss–Bonnet-type application.",
  "Ambient/PE/Renormalization.lean": "Aggregate entry point for Laurent/log expansions, finite parts, cutoff functionals, volume, and curvature integrals.",
  "Ambient/PE/Renormalization/LaurentLogExpansion.lean": "Models a finite Laurent/log expansion, parity conditions, coefficient support, and logarithmic terms.",
  "Ambient/PE/Renormalization/FinitePart.lean": "Defines the finite part as the constant Laurent coefficient and the log anomaly as the logarithmic coefficient.",
  "Ambient/PE/Renormalization/CutoffFunctional.lean": "Packages cutoff-dependent quantities whose asymptotic expansion defines a renormalized value.",
  "Ambient/PE/Renormalization/Volume.lean": "Specializes cutoff functionals to renormalized PE volume and its anomaly.",
  "Ambient/PE/Renormalization/CurvatureIntegral.lean": "Specializes the finite-part framework to renormalized integrals of curvature invariants.",
  "Ambient/PE/Renormalization/DivergenceVanishing.lean": "States the weighted divergence-vanishing interface corresponding to the parity input used in Lemma 4.1.",
  "Ambient/PE/Applications.lean": "Aggregate entry point for the PE renormalized-curvature-integral theorem and Pfaffian application.",
  "Ambient/PE/Applications/CaseKhaitanLinTyrrellYuan.lean": "Assembles the formal finite-part identity corresponding to Theorem 1.4 from explicit evaluation, recursion, divergence, and renormalization interfaces.",
  "Ambient/PE/Applications/PfaffianApplication.lean": "Packages the Pfaffian-like specialization and formal Theorem 1.1 assembly.",
  "GJMSoperators/Basic.lean": "Defines the critical input/output density weights, abstract GJMS operators, and operator families of order 2k.",
  "GJMSoperators/Ambientconstruction.lean": "Packages powers of the ambient Laplacian as weighted operators and proves their weight shift under the algebraic calculus interface.",
  "GJMSoperators/Tangentiality.lean": "Proves that the kth ambient Laplacian power is tangential at weight k - n/2 and packages the resulting canonical GJMS family.",
  "PolyGJMSoperators/Basic.lean": "Defines multilinear ambient inputs/operators and basic operations for replacing or transforming input slots.",
  "PolyGJMSoperators/Homogeneity.lean": "Defines slot weights, total weight, output weight, and multihomogeneity for multilinear operators.",
  "PolyGJMSoperators/Operators.lean": "Provides core multilinear operator constructors and their evaluation rules.",
  "PolyGJMSoperators/Boundary.lean": "Defines componentwise equality of multilinear inputs on the boundary and proves its equivalence-relation laws.",
  "PolyGJMSoperators/Tangential.lean": "Defines weighted multi-tangentiality: replacing any input by a boundary-equivalent representative does not change the restricted output.",
  "PolyGJMSoperators/Bidifferential.lean": "Specializes the multilinear framework to two inputs, two weights, and bidifferential tangentiality.",
  "PolyGJMSoperators/LaplacianWords.lean": "Defines words built from ambient Laplacians and multiplication, together with total-power bookkeeping.",
  "PolyGJMSoperators/Tree.lean": "Aggregate entry point for rank-general left-comb Laplacian words and recurrence interfaces.",
  "PolyGJMSoperators/TreeLaplacianWords.lean": "Defines rank-general left-comb indices and evaluates the associated nested multilinear Laplacian word.",
  "PolyGJMSoperators/TreeRecurrence.lean": "Defines paths, descendants, subtree weights, defect coefficients, and the first recurrence differential for a left-comb tree.",
  "PolyGJMSoperators/TreeDefectCancellation.lean": "States an abstract interface that turns the path-wise recurrence into cancellation of slot defects and hence tangentiality.",
  "PolyGJMSoperators/TreeChainComplex.lean": "Packages first-kernel and Euler-characteristic targets for the prospective rank-general recurrence complex.",
  "PolyGJMSoperators/LinearCombination.lean": "Defines finite linear combinations of multilinear ambient operators and their evaluation.",
  "PolyGJMSoperators/PolyLaplacianCombination.lean": "Specializes linear combinations to Laplacian words of fixed total order.",
  "PolyGJMSoperators/OvsienkoRedou.lean": "Provides the initial bidifferential ambient ansatz and coefficient recurrence for curved Ovsienko–Redou-type operators.",
  "PolyGJMSoperators/OR.lean": "Aggregate entry point for OR indices, recurrence, defect cancellation, coefficients, and the closed operator.",
  "PolyGJMSoperators/OR/Index.lean": "Defines triples (a,b,c) of Laplacian exponents with a+b+c=N and the elementary moves between neighboring terms.",
  "PolyGJMSoperators/OR/OperatorData.lean": "Packages the weighted OR operator data and the Laplacian word attached to each OR index.",
  "PolyGJMSoperators/OR/DefectCancellation.lean": "Encodes coefficient conditions that cancel Q-commutator defects in the two input slots.",
  "PolyGJMSoperators/OR/ClosedOperator.lean": "Builds the closed OR linear combination from its coefficient system and packages its stated properties.",
  "PolyGJMSoperators/OR/Coefficients/Parameters.lean": "Defines the dimension, weight, and order parameters appearing in the OR coefficient formulas.",
  "PolyGJMSoperators/OR/Coefficients/Combinatorics.lean": "Provides factorial, Pochhammer-type, and rational combinatorial identities used by the coefficient proof.",
  "PolyGJMSoperators/OR/Coefficients/Recurrence.lean": "States the neighboring-index recurrence equations required for OR defect cancellation.",
  "PolyGJMSoperators/OR/Coefficients/RatioLemmas.lean": "Proves ratios of neighboring closed coefficients needed to discharge the recurrence equations.",
  "PolyGJMSoperators/OR/Coefficients/ClosedFormula.lean": "Defines the proposed closed product formula for OR coefficients.",
  "PolyGJMSoperators/OR/Coefficients/ClosedSatisfiesRecurrence.lean": "Proves that the closed coefficient formula satisfies the encoded OR recurrence relations.",
  "Juhlformula/Juhloperators/Basic.lean": "Defines ordered compositions I=(I_1,...,I_r) of an integer N.",
  "Juhlformula/Juhloperators/Composition.lean": "Evaluates an ordered composition as P_{2I_1} composed with ... composed with P_{2I_r}.",
  "Juhlformula/Juhloperators/GJMSComposition.lean": "Specializes ordered compositions to the canonical ambient GJMS family.",
  "Juhlformula/Juhloperators/Coefficients.lean": "Defines abstract composition coefficients and a placeholder closed coefficient system.",
  "Juhlformula/Juhlcombinatorics.lean": "Aggregate entry point for the formal obstruction recursion and OR–Juhl bridge.",
  "Juhlformula/Juhlcombinatorics/FormalJets.lean": "Defines a purely formal expression language for metric jets, Taylor denominators, and obstruction coefficients.",
  "Juhlformula/Juhlcombinatorics/Recursion.lean": "Performs syntax-level recursive elimination of normal jets and defines the formal obstruction expression formalP.",
  "Juhlformula/Juhlcombinatorics/LowOrderCheck.lean": "Normalizes formal expressions and verifies the encoded raw P2 and P4 low-order identities.",
  "Juhlformula/Juhlcombinatorics/FormalStatement.lean": "Defines the data of a formal Juhl right-hand side and the proposition that formalP equals that expression.",
  "Juhlformula/Juhlcombinatorics/ORBridge.lean": "Defines an abstract termwise bridge between a formal Juhl right-hand side and an OR right-hand side.",
  "Juhlformula/Juhlcombinatorics/CurvedORJuhlFormula.lean": "Composes FormalJuhlStatement with ORBridge to obtain the final formal curved OR–Juhl equality.",
};

const formulas = {
  "Ambient/FG/NormalForm.lean": "\\widetilde g = 2\\rho\\,dt^2 + 2t\\,dt\\,d\\rho + t^2 g_\\rho",
  "Ambient/FG/Laplacian.lean": "Q = 2\\rho t^2",
  "Ambient/FG/Commutators.lean": "XQ=2Q,\\qquad [X,\\widetilde\\Delta]=-2\\widetilde\\Delta",
  "Ambient/PE/NormalForm.lean": "g_+ = r^{-2}(dr^2+h_r)",
  "Ambient/PE/Basic.lean": "\\operatorname{Ric}(g_+)=-n g_+",
  "GJMSoperators/Basic.lean": "P_{2k}:\\mathcal E[k-n/2]\\longrightarrow\\mathcal E[-k-n/2]",
  "GJMSoperators/Tangentiality.lean": "f_1-f_2=Qh\\;\\Longrightarrow\\;i^*(\\widetilde\\Delta^k f_1)=i^*(\\widetilde\\Delta^k f_2)",
  "PolyGJMSoperators/OR/Index.lean": "a+b+c=N",
  "PolyGJMSoperators/TreeLaplacianWords.lean": "\\widetilde\\Delta^{a_0}(\\widetilde\\Delta^{a_1}((\\widetilde\\Delta^{a_2}u_0)(\\widetilde\\Delta^{a_3}u_1))\\cdots)",
  "Juhlformula/Juhloperators/Composition.lean": "P_{2I}=P_{2I_1}\\circ\\cdots\\circ P_{2I_r}",
  "Ambient/PE/Renormalization/FinitePart.lean": "\\operatorname{FP}_{\\varepsilon\\to0}F(\\varepsilon)=[\\varepsilon^0]F(\\varepsilon)",
};

function walk(dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
    const full = path.join(dir, entry.name);
    return entry.isDirectory() ? walk(full) : [full];
  });
}

function rel(file) { return path.relative(sourceRoot, file).split(path.sep).join("/"); }
function notePath(file) { return path.join(notesRoot, file.replace(/\.lean$/, ".json")); }
function words(name) { return name.replace(/_/g, " ").replace(/([a-z0-9])([A-Z])/g, "$1 $2"); }

function cleanDocComment(raw) {
  const cleaned = raw
    .split(/\r?\n/)
    .map((line) => line.replace(/^\s*\*?\s?/, "").trim())
    .filter((line) => !/^#{1,6}\s/.test(line))
    .join(" ")
    .replace(/\[([^\]]+)\]\([^\)]+\)/g, "$1")
    .replace(/`([^`]+)`/g, "$1")
    .replace(/\*\*([^*]+)\*\*/g, "$1")
    .replace(/\*([^*]+)\*/g, "$1")
    .replace(/\s+/g, " ")
    .trim();
  if (cleaned.length <= 900) return cleaned;
  const shortened = cleaned.slice(0, 900);
  return `${shortened.slice(0, Math.max(shortened.lastIndexOf(". "), 760) + 1).trim()}...`;
}

function docCommentBefore(source, declarationOffset) {
  const prefix = source.slice(0, declarationOffset);
  const comments = [...prefix.matchAll(/\/--([\s\S]*?)-\//g)];
  const last = comments.at(-1);
  if (!last) return "";
  const after = prefix.slice(last.index + last[0].length)
    .replace(/@\[[\s\S]*?\]/g, "")
    .trim();
  return after ? "" : cleanDocComment(last[1]);
}

function findTopLevelColon(value) {
  let round = 0; let square = 0; let curly = 0;
  for (let i = 0; i < value.length; i++) {
    const char = value[i];
    if (char === "(") round++;
    else if (char === ")") round--;
    else if (char === "[") square++;
    else if (char === "]") square--;
    else if (char === "{") curly++;
    else if (char === "}") curly--;
    else if (char === ":" && round === 0 && square === 0 && curly === 0) return i;
  }
  return -1;
}

function findTopLevelMarker(value, marker) {
  let round = 0; let square = 0; let curly = 0;
  for (let i = 0; i <= value.length - marker.length; i++) {
    const char = value[i];
    if (char === "(") round++;
    else if (char === ")") round--;
    else if (char === "[") square++;
    else if (char === "]") square--;
    else if (char === "{") curly++;
    else if (char === "}") curly--;
    if (round === 0 && square === 0 && curly === 0 && value.startsWith(marker, i)) return i;
  }
  return -1;
}

function extractBinders(value) {
  const binders = [];
  let rest = value.trim();
  while (["(", "{", "["].includes(rest[0])) {
    const opener = rest[0];
    const closer = opener === "(" ? ")" : opener === "{" ? "}" : "]";
    let depth = 0; let end = -1;
    for (let i = 0; i < rest.length; i++) {
      if (rest[i] === opener) depth++;
      else if (rest[i] === closer && --depth === 0) { end = i; break; }
    }
    if (end < 0) break;
    const content = rest.slice(1, end).trim();
    const colon = findTopLevelColon(content);
    binders.push({
      explicit: opener === "(",
      instance: opener === "[",
      names: (colon >= 0 ? content.slice(0, colon) : content).trim().split(/\s+/).filter(Boolean),
      type: colon >= 0 ? content.slice(colon + 1).trim() : "",
    });
    rest = rest.slice(end + 1).trim();
  }
  const colon = findTopLevelColon(rest);
  return {
    binders,
    result: colon >= 0 ? rest.slice(colon + 1).trim() : rest.trim(),
  };
}

function binderPhrase(binder) {
  const names = binder.names.map((name) => name.replace(/^_/, "")).filter(Boolean).join(", ");
  const type = binder.type.trim();
  if (!names) return "";
  if (type === "\u211D" || type === "Real") return `${names} in the real numbers`;
  if (type === "\u2115" || type === "Nat") return `${names} in the natural numbers`;
  if (type === "\u2124" || type === "Int") return `${names} in the integers`;
  if (/^Type\b/.test(type)) return `${names} a type`;
  if (/Finset/.test(type)) return `${names} a finite set`;
  if (/List/.test(type)) return `${names} a finite list`;
  if (/Prop$/.test(type)) return `${names} a proposition`;
  return `${names} of type ${leanToWords(type)}`;
}

function parameterPhrase(binders) {
  const phrases = binders.filter((binder) => !binder.instance).map(binderPhrase).filter(Boolean);
  if (!phrases.length) return "";
  if (phrases.length === 1) return `For ${phrases[0]}`;
  return `For ${phrases.slice(0, -1).join(", ")}, and ${phrases.at(-1)}`;
}

function leanToWords(value) {
  return value
    .replace(new RegExp(`\\(([^():]+)\\s*:\\s*(?:\\u211D|Real)\\)`, "g"), "$1")
    .replace(new RegExp(`\\(([^():]+)\\s*:\\s*(?:\\u2115|Nat)\\)`, "g"), "$1")
    .replace(/\bCalConf\.n\b/g, "the dimension n of the ambient calculus")
    .replace(/\binputWeight\b/g, "input weight")
    .replace(/\boutputWeight\b/g, "output weight")
    .replace(/\blaplacian\b/gi, "ambient Laplacian")
    .replace(/\blapPow\b/g, "power of the ambient Laplacian")
    .replace(/\brestrict\b/g, "restriction to the null cone")
    .replace(/\bfun\s+([A-Za-z][A-Za-z0-9_']*)\s*=>/g, "the function sending $1 to ")
    .replace(/\bforall\b/g, "for every ")
    .replace(/->/g, " maps to ")
    .replace(/=>/g, " maps to ")
    .replace(/\u2200/g, "for every ")
    .replace(/\u2203/g, "there exists ")
    .replace(/\u2194/g, " if and only if ")
    .replace(/\u2192/g, " maps to ")
    .replace(/\u2227/g, " and ")
    .replace(/\u2228/g, " or ")
    .replace(/\u00AC/g, " not ")
    .replace(/\u2260/g, " is not equal to ")
    .replace(/\u2264/g, " is at most ")
    .replace(/\u2265/g, " is at least ")
    .replace(/\u2208/g, " belongs to ")
    .replace(/\u2286/g, " is contained in ")
    .replace(/=/g, " equals ")
    .replace(/\+/g, " plus ")
    .replace(/\s-\s/g, " minus ")
    .replace(/\*/g, " times ")
    .replace(/\//g, " divided by ")
    .replace(/\^/g, " to the power ")
    .replace(/\u211D/g, "the real numbers")
    .replace(/\u2115/g, "the natural numbers")
    .replace(/\u2124/g, "the integers")
    .replace(/([a-z0-9])([A-Z])/g, "$1 $2")
    .replace(/_/g, " ")
    .replace(/[{}()\[\]]/g, " ")
    .replace(/\s+/g, " ")
    .replace(/\s+,/g, ",")
    .trim();
}

function latexIdentifier(token) {
  if (/^\d+$/.test(token)) return token;
  if (token.length === 1) return token;
  const known = {
    inputWeight: "w_{\\mathrm{in}}", outputWeight: "w_{\\mathrm{out}}",
    calculusInputWeight: "w_{\\mathrm{in}}", calculusOutputWeight: "w_{\\mathrm{out}}",
    laplacian: "\\widetilde{\\Delta}", lapPow: "\\widetilde{\\Delta}^{k}",
    Q: "Q", X: "X", Prop: "\\mathrm{Prop}", Type: "\\mathrm{Type}",
    Nat: "\\mathbb{N}", Int: "\\mathbb{Z}", Rat: "\\mathbb{Q}", Real: "\\mathbb{R}",
    True: "\\mathrm{True}", False: "\\mathrm{False}",
  };
  if (known[token]) return known[token];
  if (token.includes(".")) {
    const parts = token.split(".");
    const last = parts.pop();
    if (last.length === 1) return `${last}_{\\mathrm{${parts.at(-1).replace(/_/g, "\\_")}}}`;
    const base = parts.shift();
    const prefix = latexIdentifier(base);
    const middle = parts.map((part) => `\\operatorname{${part.replace(/_/g, "\\_")}}`).join(".");
    return `${prefix}${middle ? `.${middle}` : ""}.\\operatorname{${last.replace(/_/g, "\\_")}}`;
  }
  return `\\operatorname{${token.replace(/_/g, "\\_")}}`;
}

function leanToLatex(value) {
  let result = value
    .replace(new RegExp(`\\(([^():]+)\\s*:\\s*(?:\\u211D|Real)\\)`, "g"), "$1")
    .replace(new RegExp(`\\(([^():]+)\\s*:\\s*(?:\\u2115|Nat)\\)`, "g"), "$1")
    .replace(/\bfun\s+([A-Za-z][A-Za-z0-9_']*)\s*=>/g, "$1 \u21A6 ")
    .replace(/\bforall\b/g, "\u2200")
    .replace(/->/g, "\u2192")
    .replace(/[A-Za-z][A-Za-z0-9_'.]*/g, latexIdentifier)
    .replace(/\u0394\u0303/g, "\\widetilde{\\Delta}")
    .replace(/\u211D/g, "\\mathbb{R}")
    .replace(/\u2115/g, "\\mathbb{N}")
    .replace(/\u2124/g, "\\mathbb{Z}")
    .replace(/\u211A/g, "\\mathbb{Q}")
    .replace(/\u2200/g, "\\forall ")
    .replace(/\u2203/g, "\\exists ")
    .replace(/\u2194/g, "\\Longleftrightarrow")
    .replace(/\u2192/g, "\\longrightarrow")
    .replace(/\u21A6/g, "\\longmapsto")
    .replace(/\u2227/g, "\\land")
    .replace(/\u2228/g, "\\lor")
    .replace(/\u00AC/g, "\\neg ")
    .replace(/\u2260/g, "\\ne")
    .replace(/\u2264/g, "\\le")
    .replace(/\u2265/g, "\\ge")
    .replace(/\u2208/g, "\\in")
    .replace(/\u2286/g, "\\subseteq")
    .replace(/\u2211/g, "\\sum")
    .replace(/\u220F/g, "\\prod")
    .replace(/\u00B7/g, "\\cdot")
    .replace(/\*/g, "\\cdot")
    .replace(/:=/g, "=")
    .replace(/:/g, "\\colon ");
  return result.replace(/\s+/g, " ").trim();
}

function subjectFormula(name, binders) {
  const args = binders
    .filter((binder) => binder.explicit && !binder.instance)
    .flatMap((binder) => binder.names)
    .filter((arg) => !arg.startsWith("_"));
  const subject = latexIdentifier(name);
  return args.length ? `${subject}(${args.join(",")})` : subject;
}

function quantifiedFormula(binders, result) {
  const declarations = binders.map((binder) => {
    if (binder.type) return `${binder.names.join(",")}\\colon ${leanToLatex(binder.type)}`;
    return leanToLatex(binder.names.join(" "));
  }).filter(Boolean);
  const proposition = leanToLatex(result);
  return declarations.length ? `\\forall\\,${declarations.join(",\\;")},\\quad ${proposition}` : proposition;
}

function equationFormula(name, rhs) {
  const clauses = rhs.split(/\s*\|\s*/).filter(Boolean).map((clause) => {
    const marker = clause.indexOf("=>");
    if (marker < 0) return leanToLatex(clause);
    const pattern = clause.slice(0, marker).trim();
    const value = clause.slice(marker + 2).trim();
    return `${latexIdentifier(name)}(${leanToLatex(pattern)})&=${leanToLatex(value)}`;
  });
  return clauses.length > 1 ? `\\begin{aligned}${clauses.join("\\\\")}\\end{aligned}` : clauses[0] ?? `${latexIdentifier(name)}`;
}

function extractFields(lines, kind) {
  const fields = [];
  const uncommented = lines.join("\n").replace(/\/-[\s\S]*?-\//g, "");
  lines = uncommented.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].replace(/--.*$/, "").trim();
    if (!line || line.startsWith("/-") || /^(namespace|section|end)\b/.test(line)) continue;
    if (kind === "inductive") {
      const constructor = line.match(/^\|\s*([A-Za-z][A-Za-z0-9_']*)(?:\s+(.*))?$/);
      if (constructor) fields.push({ name: constructor[1], type: constructor[2]?.trim() ?? "", constructor: true });
      continue;
    }
    const match = line.match(/^\|?\s*([A-Za-z][A-Za-z0-9_']*)\s*:\s*(.*)$/);
    if (!match) continue;
    let type = match[2].trim();
    for (let j = i + 1; j < lines.length; j++) {
      const next = lines[j].replace(/--.*$/, "").trim();
      if (!next || next.startsWith("/-") || /^\|?\s*[A-Za-z][A-Za-z0-9_']*\s*:/.test(next) || /^(namespace|section|end|deriving)\b/.test(next)) break;
      type += ` ${next}`;
      i = j;
    }
    fields.push({ name: match[1], type });
  }
  return fields;
}

function translatedDeclaration({ name, kind, doc, binders, result, rhs, fields }) {
  const parameters = parameterPhrase(binders);
  const lead = parameters ? `${parameters}, ` : "";
  const subject = words(name).toLowerCase();
  let mathematicalMeaning = doc;
  let mathematicalFormula = null;

  if (["structure", "class", "inductive"].includes(kind)) {
    const fieldDescription = kind === "inductive"
      ? fields.map((field) => field.type ? `${words(field.name)} with arguments ${leanToWords(field.type)}` : words(field.name)).join("; ")
      : fields.map((field) => `${words(field.name)}: ${leanToWords(field.type)}`).join("; ");
    if (!mathematicalMeaning) mathematicalMeaning = `A ${subject} consists of ${fieldDescription || leanToWords(result)}.`;
    else if (fieldDescription) mathematicalMeaning += kind === "inductive"
      ? ` Its constructors are: ${fieldDescription}.`
      : ` Its mathematical data are: ${fieldDescription}.`;
    if (fields.length) {
      mathematicalFormula = kind === "inductive"
        ? `${latexIdentifier(name)}::=${fields.map((field) => field.type ? `${latexIdentifier(field.name)}(${leanToLatex(field.type)})` : latexIdentifier(field.name)).join("\\mid")}`
        : `\\begin{aligned}${fields.map((field) => `${latexIdentifier(field.name)}&\\colon ${leanToLatex(field.type)}`).join("\\\\") }\\end{aligned}`;
    } else if (result) mathematicalFormula = `${latexIdentifier(name)}\\colon ${leanToLatex(result)}`;
  } else if (["def", "abbrev"].includes(kind)) {
    const usefulRhs = rhs && !/^(by|match|if|let)\b/.test(rhs) && rhs.length < 500;
    const equationRhs = usefulRhs && rhs.trim().startsWith("|");
    const rhsWords = usefulRhs ? leanToWords(rhs) : "";
    if (!mathematicalMeaning) {
      mathematicalMeaning = usefulRhs
        ? `${lead}the ${subject} is defined to be ${rhsWords}.`
        : `${lead}the ${subject} is a ${leanToWords(result)} specified by this definition.`;
    } else if (usefulRhs && !mathematicalMeaning.toLowerCase().includes(rhsWords.toLowerCase())) {
      mathematicalMeaning += ` In explicit terms, ${lead.toLowerCase()}its defining expression is ${rhsWords}.`;
    }
    mathematicalFormula = usefulRhs
      ? equationRhs ? equationFormula(name, rhs) : `${subjectFormula(name, binders)}=${leanToLatex(rhs)}`
      : `${subjectFormula(name, binders)}\\colon ${leanToLatex(result)}`;
  } else {
    const propositionWords = leanToWords(result);
    if (!mathematicalMeaning) mathematicalMeaning = `${lead}${propositionWords}.`;
    else if (propositionWords && !mathematicalMeaning.toLowerCase().includes(propositionWords.toLowerCase())) {
      mathematicalMeaning += ` In symbols, the proposition is the statement displayed below.`;
    }
    mathematicalFormula = quantifiedFormula(binders, result);
  }

  mathematicalMeaning = mathematicalMeaning
    .replace(/\s+/g, " ")
    .replace(/\s+\./g, ".")
    .trim();
  return { mathematicalMeaning, mathematicalFormula };
}

function statusFor(file, source) {
  if (file.includes("Juhlformula/Juhlcombinatorics/ORBridge") || file.includes("CurvedORJuhlFormula") || file.includes("TreeDefectCancellation") || file.includes("TreeChainComplex")) return "scaffold";
  if (file.includes("Ambient/FG/") && !file.endsWith("Commutators.lean") || file.includes("Ambient/PE/")) return source.includes("structure ") || source.includes("class ") ? "verified-under-interface" : "scaffold";
  if (file.includes("GJMSoperators/") || file.includes("PolyGJMSoperators/OR/DefectCancellation") || file.includes("ClosedOperator")) return "verified-under-interface";
  if (file.endsWith(".lean") && (file.endsWith("FG.lean") || file.endsWith("PE.lean") || file.endsWith("OR.lean") || file.endsWith("Tree.lean") || file.endsWith("Juhlcombinatorics.lean"))) return "scaffold";
  return "verified";
}

function referenceFor(file) {
  if (file.startsWith("Ambient/PE/Applications") || file.startsWith("Ambient/PE/Invariants") || file.startsWith("Ambient/PE/Renormalization")) return [{ referenceId: "CaseKhaitanLinTyrrellYuan-2024", locator: "Proposition 3.7, Proposition 3.10, Lemma 4.1, and Theorems 1.1/1.4 as applicable", note: "Primary source for the renormalized-curvature-integral mechanism represented by these modules." }, { referenceId: "FG-AmbientMetric", locator: "Chapter 4", note: "Background for the ambient/Poincaré correspondence." }];
  if (file.startsWith("Ambient/PE/")) return [{ referenceId: "FG-AmbientMetric", locator: "Chapter 4, Poincaré metrics", note: "Source for Poincaré normal form and its relation to straight ambient metrics." }];
  if (file.startsWith("Ambient/") || file.startsWith("Conformal/")) return [{ referenceId: "FG-AmbientMetric", locator: "Chapters 2–3, ambient space and normal form", note: "Geometric source for the ambient bundle, homogeneity, normal form, and commutator calculations." }];
  if (file.startsWith("GJMSoperators/")) return [{ referenceId: "GJMS-1992", locator: "pp. 557–565, ambient extension construction", note: "Original construction of conformally invariant powers of the Laplacian." }, { referenceId: "FG-AmbientMetric", locator: "Ambient Laplacian and homogeneous extension discussion", note: "Ambient-metric background for the formal construction." }];
  if (file.includes("Tree")) return [{ referenceId: "CaseCieslak-2025", locator: "Main ambient construction and tangentiality results", note: "Motivation for rank-general nested Laplacian words; the Lean tree complex goes beyond what is currently instantiated." }];
  if (file.startsWith("PolyGJMSoperators/OR") || file.endsWith("OvsienkoRedou.lean")) return [{ referenceId: "OvsienkoRedou-2001", locator: "Classification of invariant bilinear differential operators", note: "Flat-model origin of the coefficient family." }, { referenceId: "CaseLinYuan-2022", locator: "Ambient classification and curved construction", note: "Primary curved ambient source for the encoded OR recurrence." }];
  if (file.startsWith("PolyGJMSoperators/")) return [{ referenceId: "CaseLinYuan-2022", locator: "Ambient bidifferential operator setup", note: "Source for multilinear tangentiality and Laplacian-word constructions." }];
  if (file.startsWith("Juhlformula/Juhloperators")) return [{ referenceId: "Juhl-2011", locator: "Composition formulas for GJMS operators", note: "Source for ordered GJMS compositions and coefficients." }, { referenceId: "FeffermanGraham-Juhl-2012", locator: "Direct ambient proof of Juhl's formulas", note: "Ambient interpretation of the composition formula." }];
  return [{ referenceId: "ChernYan-2024", locator: "Formal Juhl-type formula and OR bridge", note: "Primary source for the intended curved OR–Juhl identity." }, { referenceId: "Juhl-2011", locator: "GJMS composition formulas", note: "Source for the Juhl side of the formal syntax." }];
}

function limitationFor(status) {
  if (status === "scaffold") return "This file establishes syntax, aggregate imports, or an abstract bridge. It must not be read as a derivation of the corresponding geometric theorem from concrete tensor and analytic data.";
  if (status === "verified-under-interface") return "The displayed Lean results are checked relative to structures, typeclasses, certificates, or model laws supplied as hypotheses. The module does not by itself derive every interface field from a concrete geometric backend.";
  return "Verified means that Lean checks the propositions encoded in this file and their imported assumptions. It does not assert that the present formal statement exhausts every analytic hypothesis or convention in the cited literature.";
}

const leanFiles = walk(sourceRoot).filter((f) => f.endsWith(".lean"));
const modules = new Map();

for (const full of leanFiles) {
  const file = rel(full);
  const source = fs.readFileSync(full, "utf8");
  const lines = source.split(/\r?\n/);
  const imports = [...source.matchAll(/^import ConformalCovariantOperators\.([^\s]+)$/gm)].map((m) => `${m[1].replaceAll(".", "/")}.lean`);
  const declarationStarts = [];
  const declarationPattern = /^\s*(?:noncomputable\s+)?(structure|class|def|abbrev|inductive|theorem|lemma|axiom)\s+([^\s(:{]+)/;
  for (let i = 0; i < lines.length; i++) {
    const match = lines[i].match(declarationPattern);
    if (match) declarationStarts.push({ line: i, match });
  }
  const lineOffsets = [];
  let cursor = 0;
  for (const line of lines) {
    const offset = source.indexOf(line, cursor);
    lineOffsets.push(offset >= 0 ? offset : cursor);
    cursor = (offset >= 0 ? offset : cursor) + line.length;
  }
  const correspondence = [];
  for (let index = 0; index < declarationStarts.length; index++) {
    const { line: start, match } = declarationStarts[index];
    const end = declarationStarts[index + 1]?.line ?? lines.length;
    const blockLines = lines.slice(start, end);
    const headerParts = [];
    const bodyLines = [];
    let bodyStarted = false;
    const structuredDeclaration = ["structure", "class", "inductive"].includes(match[1]);
    for (const rawLine of blockLines) {
      const code = (rawLine.includes("/-") ? rawLine : rawLine.replace(/--.*$/, "")).trim();
      if (!code && bodyStarted && bodyLines.length && !structuredDeclaration) break;
      if (!code) continue;
      if (bodyStarted) {
        if (!structuredDeclaration && (code.startsWith("/-") || code.startsWith("@[") || /^(namespace|section|end)\b/.test(code))) break;
        bodyLines.push(code);
        continue;
      }
      const definitionMarker = findTopLevelMarker(code, ":=");
      const whereMarker = code.match(/\s+where\s*$/);
      if (definitionMarker >= 0) {
        headerParts.push(code.slice(0, definitionMarker).trim());
        const remainder = code.slice(definitionMarker + 2).trim();
        if (remainder) bodyLines.push(remainder);
        bodyStarted = true;
      } else if (whereMarker) {
        headerParts.push(code.slice(0, whereMarker.index).trim());
        bodyStarted = true;
      } else if (code === "where") {
        bodyStarted = true;
      } else if (code.startsWith("|")) {
        bodyLines.push(code);
        bodyStarted = true;
      } else if (code.startsWith("/-") || code.startsWith("@[") || /^(namespace|section|end)\b/.test(code)) {
        break;
      } else {
        headerParts.push(code);
      }
    }
    const header = headerParts.join(" ").replace(/\s+/g, " ").trim();
    const name = match[2];
    const kind = match[1];
    const withoutPrefix = header.replace(new RegExp(`^(?:noncomputable\\s+)?${kind}\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`), "").trim();
    const { binders, result } = extractBinders(withoutPrefix);
    const rhs = bodyLines.join(" ").replace(/\s+/g, " ").trim();
    const fields = ["structure", "class", "inductive"].includes(kind) ? extractFields(bodyLines, kind) : [];
    const doc = docCommentBefore(source, lineOffsets[start]);
    const translation = translatedDeclaration({ name, kind, doc, binders, result, rhs, fields });
    correspondence.push({
      leanDeclaration: name,
      kind,
      ...translation,
      leanType: header,
      line: start + 1,
    });
  }
  modules.set(file, { full, source, lines, imports, correspondence });
}

for (const [file, module] of modules) {
  module.usedBy = [...modules.entries()].filter(([, other]) => other.imports.includes(file)).map(([otherFile]) => otherFile);
}

fs.rmSync(notesRoot, { recursive: true, force: true });
const index = [];
for (const [file, module] of modules) {
  const status = statusFor(file, module.source);
  const title = path.basename(file, ".lean");
  const summary = descriptions[file] ?? `Documents the ${words(title)} layer of ${path.dirname(file).replaceAll("/", " ")}. This description is intentionally conservative and should receive mathematical review.`;
  const note = {
    file,
    title,
    status: descriptions[file] ? status : "needs-review",
    summary,
    mathematicalContent: [
      { heading: "Mathematical role", body: summary, formula: formulas[file] ?? null },
      { heading: "How to read the translation", body: `The correspondence below follows ${file} declaration by declaration. A definition is translated by its defining expression, a theorem by its quantified proposition, and a structure, class, or inductive type by the mathematical data encoded in its fields or constructors. The original Lean signature remains visible beside every translation.`, formula: null },
    ],
    correspondence: module.correspondence,
    prerequisites: module.imports.filter((x) => modules.has(x)),
    usedBy: module.usedBy,
    references: referenceFor(file),
    limitations: limitationFor(descriptions[file] ? status : "needs-review"),
  };
  const output = notePath(file);
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, `${JSON.stringify(note, null, 2)}\n`);
  index.push({ file, title, status: note.status, summary, declarations: note.correspondence.map((x) => x.leanDeclaration), referenceIds: note.references.map((x) => x.referenceId) });
}
fs.writeFileSync(path.join(notesRoot, "module-index.json"), `${JSON.stringify(index.sort((a, b) => a.file.localeCompare(b.file)), null, 2)}\n`);
console.log(`Generated ${index.length} module notes.`);
