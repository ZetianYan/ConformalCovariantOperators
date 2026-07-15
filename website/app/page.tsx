"use client";

import { useEffect, useMemo, useRef, useState } from "react";

type MapNode = { name: string; file?: string; children?: MapNode[] };
type Status = "verified" | "verified-under-interface" | "scaffold" | "planned" | "needs-review";
type Correspondence = { leanDeclaration: string; kind: string; mathematicalMeaning: string; leanType: string; line: number };
type ModuleNote = {
  file: string; title: string; status: Status; summary: string;
  mathematicalContent: { heading: string; body: string; formula: string | null }[];
  correspondence: Correspondence[]; prerequisites: string[]; usedBy: string[];
  references: { referenceId: string; locator: string; note: string }[]; limitations: string;
};
type Reference = { id: string; authors: string; title: string; year: number; publisher: string; url: string; citation: string };
type ModuleIndex = { file: string; title: string; status: Status; summary: string; declarations: string[]; referenceIds: string[] };

declare global { interface Window { katex?: { render: (formula: string, element: HTMLElement, options: Record<string, unknown>) => void } } }

const statusLabels: Record<Status, string> = {
  verified: "Verified",
  "verified-under-interface": "Verified under interface",
  scaffold: "Scaffold",
  planned: "Planned",
  "needs-review": "Needs review",
};

const projectMap: MapNode = { name: "ConformalCovariantOperators", children: [
  { name: "Conformal", children: [
    { name: "Basic", file: "Conformal/Basic.lean" }, { name: "Density", file: "Conformal/Density.lean" }
  ]},
  { name: "Ambient", children: [
    { name: "Ambientbasic", file: "Ambient/Ambientbasic.lean" }, { name: "Ambientdensity", file: "Ambient/Ambientdensity.lean" },
    { name: "Ambientoperator", file: "Ambient/Ambientoperator.lean" }, { name: "Ambienttangential", file: "Ambient/Ambienttangential.lean" },
    { name: "FG", file: "Ambient/FG.lean", children: [
      "Index","NormalForm","InverseMetric","Christoffel","Laplacian","Commutators","CalculusInstance","RicciNormalForm","FormalJets","Recursion","Obstruction"
    ].map(name => ({ name, file: `Ambient/FG/${name}.lean` })) },
    { name: "PE", file: "Ambient/PE.lean", children: [
      ...["Basic","DefiningFunction","NormalForm","MetricComponents","EinsteinEquation","AmbientBridge"].map(name => ({ name, file: `Ambient/PE/${name}.lean` })),
      { name: "Invariants", file: "Ambient/PE/Invariants.lean", children: ["RiemannianInvariant","Straightenable","LaplacianRecursion","NaturalDivergence","Pfaffian"].map(name => ({ name, file: `Ambient/PE/Invariants/${name}.lean` })) },
      { name: "Renormalization", file: "Ambient/PE/Renormalization.lean", children: ["LaurentLogExpansion","FinitePart","CutoffFunctional","Volume","CurvatureIntegral","DivergenceVanishing"].map(name => ({ name, file: `Ambient/PE/Renormalization/${name}.lean` })) },
      { name: "Applications", file: "Ambient/PE/Applications.lean", children: ["CaseKhaitanLinTyrrellYuan","PfaffianApplication"].map(name => ({ name, file: `Ambient/PE/Applications/${name}.lean` })) }
    ]}
  ]},
  { name: "GJMSoperators", children: ["Basic","Ambientconstruction","Tangentiality"].map(name => ({ name, file: `GJMSoperators/${name}.lean` })) },
  { name: "PolyGJMSoperators", children: [
    ...["Basic","Homogeneity","Operators","Boundary","Tangential","Bidifferential","LaplacianWords"].map(name => ({ name, file: `PolyGJMSoperators/${name}.lean` })),
    { name: "Tree", file: "PolyGJMSoperators/Tree.lean", children: ["TreeLaplacianWords","TreeRecurrence","TreeDefectCancellation","TreeChainComplex"].map(name => ({ name, file: `PolyGJMSoperators/${name}.lean` })) },
    ...["LinearCombination","PolyLaplacianCombination","OvsienkoRedou"].map(name => ({ name, file: `PolyGJMSoperators/${name}.lean` })),
    { name: "OR", file: "PolyGJMSoperators/OR.lean", children: [
      ...["Index","OperatorData","DefectCancellation","ClosedOperator"].map(name => ({ name, file: `PolyGJMSoperators/OR/${name}.lean` })),
      { name: "Coefficients", children: ["Parameters","Combinatorics","Recurrence","RatioLemmas","ClosedFormula","ClosedSatisfiesRecurrence"].map(name => ({ name, file: `PolyGJMSoperators/OR/Coefficients/${name}.lean` })) }
    ]}
  ]},
  { name: "Juhlformula", children: [
    { name: "Juhloperators", children: ["Basic","Composition","GJMSComposition","Coefficients"].map(name => ({ name, file: `Juhlformula/Juhloperators/${name}.lean` })) },
    { name: "Juhlcombinatorics", file: "Juhlformula/Juhlcombinatorics.lean", children: ["FormalJets","Recursion","LowOrderCheck","FormalStatement","ORBridge","CurvedORJuhlFormula"].map(name => ({ name, file: `Juhlformula/Juhlcombinatorics/${name}.lean` })) }
  ]}
]};

const branchDescriptions: Record<string, string> = {
  Conformal: "Conformal structures and density bundles",
  Ambient: "Ambient geometry, FG calculus, and PE renormalization",
  GJMSoperators: "Canonical ambient GJMS operators and tangentiality",
  PolyGJMSoperators: "Poly-Laplacian words, tree recurrence, and OR operators",
  Juhlformula: "Composition and formal obstruction sides of Juhl formulas",
};

function countFiles(node: MapNode): number { return (node.file?.endsWith(".lean") ? 1 : 0) + (node.children?.reduce((n, x) => n + countFiles(x), 0) ?? 0); }
function findNodeByFile(node: MapNode, file: string): MapNode | null {
  if (node.file === file) return node;
  for (const child of node.children ?? []) { const found = findNodeByFile(child, file); if (found) return found; }
  return null;
}

function Formula({ value }: { value: string }) {
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const render = () => { if (ref.current && window.katex) window.katex.render(value, ref.current, { throwOnError: false, displayMode: true }); };
    if (window.katex) { render(); return; }
    if (!document.getElementById("katex-css")) {
      const link = document.createElement("link"); link.id = "katex-css"; link.rel = "stylesheet"; link.href = "https://cdn.jsdelivr.net/npm/katex@0.16.22/dist/katex.min.css"; document.head.appendChild(link);
    }
    let script = document.getElementById("katex-script") as HTMLScriptElement | null;
    if (!script) { script = document.createElement("script"); script.id = "katex-script"; script.src = "https://cdn.jsdelivr.net/npm/katex@0.16.22/dist/katex.min.js"; script.defer = true; document.head.appendChild(script); }
    script.addEventListener("load", render, { once: true });
    return () => script?.removeEventListener("load", render);
  }, [value]);
  return <div className="mathFormula" ref={ref}>{value}</div>;
}

function TreeNode({ node, depth, onOpen }: { node: MapNode; depth: number; onOpen: (node: MapNode) => void }) {
  const [open, setOpen] = useState(depth < 2);
  const hasChildren = !!node.children?.length;
  function activate() { if (node.file) onOpen(node); else if (hasChildren) setOpen(x => !x); }
  return <li className={`treeNode depth-${Math.min(depth,4)}`}>
    <div className="nodeLine">
      <button className={`mapButton ${node.file ? "hasFile" : "folder"}`} onClick={activate} title={node.file ? `Open ${node.file}` : `${open ? "Collapse" : "Expand"} ${node.name}`}>
        <span className="nodeGlyph">{depth === 0 ? "λ" : hasChildren ? "◇" : "•"}</span>
        <span>{node.name}</span>
        {node.file && <small>LEAN</small>}
      </button>
      {hasChildren && <button className="toggle" onClick={() => setOpen(x => !x)} aria-label={`${open ? "Collapse" : "Expand"} ${node.name}`}>{open ? "−" : "+"}</button>}
    </div>
    {hasChildren && open && <ul>{node.children!.map((child, i) => <TreeNode key={`${child.name}-${i}`} node={child} depth={depth + 1} onOpen={onOpen}/>)}</ul>}
  </li>;
}

export default function Home() {
  const [selected, setSelected] = useState<MapNode | null>(null);
  const [code, setCode] = useState("");
  const [note, setNote] = useState<ModuleNote | null>(null);
  const [references, setReferences] = useState<Reference[]>([]);
  const [moduleIndex, setModuleIndex] = useState<ModuleIndex[]>([]);
  const [loading, setLoading] = useState(false);
  const [query, setQuery] = useState("");
  const [mobileTab, setMobileTab] = useState<"math" | "source" | "refs">("math");
  const total = useMemo(() => countFiles(projectMap), []);
  const basePath = process.env.NEXT_PUBLIC_BASE_PATH ?? "";

  function openModule(node: MapNode) {
    setLoading(true); setCode(""); setNote(null); setSelected(node); setMobileTab("math");
    if (node.file && typeof window !== "undefined") { const url = new URL(window.location.href); url.searchParams.set("module", node.file); window.history.replaceState(null, "", url); }
  }

  function closeModule() {
    setSelected(null); setNote(null);
    if (typeof window !== "undefined") { const url = new URL(window.location.href); url.searchParams.delete("module"); window.history.replaceState(null, "", url); }
  }

  function openFile(file: string) { const node = findNodeByFile(projectMap, file); if (node) openModule(node); }

  useEffect(() => {
    Promise.all([
      fetch(`${basePath}/references.json`).then((r) => r.json()),
      fetch(`${basePath}/module-notes/module-index.json`).then((r) => r.json()),
    ]).then(([refs, index]) => { setReferences(refs); setModuleIndex(index); });
    const requested = new URL(window.location.href).searchParams.get("module");
    if (requested) { const node = findNodeByFile(projectMap, requested); if (node) Promise.resolve().then(() => { setLoading(true); setSelected(node); }); }
  }, [basePath]);

  useEffect(() => {
    if (!selected?.file) return;
    const noteFile = selected.file.replace(/\.lean$/, ".json");
    Promise.all([
      fetch(`${basePath}/source/${selected.file}`).then((r) => r.text()),
      fetch(`${basePath}/module-notes/${noteFile}`).then((r) => r.json()),
    ]).then(([source, moduleNote]) => { setCode(source); setNote(moduleNote); }).catch(() => setCode("Unable to load this module workspace.")).finally(() => setLoading(false));
  }, [selected, basePath]);

  const referenceById = useMemo(() => new Map(references.map((ref) => [ref.id, ref])), [references]);
  const results = useMemo(() => {
    const needle = query.trim().toLowerCase(); if (!needle) return [];
    return moduleIndex.filter((item) => {
      const authors = item.referenceIds.map((id) => referenceById.get(id)?.authors ?? "").join(" ");
      return [item.file, item.title, item.summary, item.status, ...item.declarations, authors].join(" ").toLowerCase().includes(needle);
    });
  }, [query, moduleIndex, referenceById]);

  function jumpToLine(line: number) { setMobileTab("source"); setTimeout(() => document.getElementById(`code-line-${line}`)?.scrollIntoView({ behavior: "smooth", block: "center" }), 80); }

  return <main>
    <header className="nav"><a href="#home" className="wordmark"><span>λ</span><b>Conformal Covariant Operators</b></a><nav><a href="#introduction">Introduction</a><a href="#project-map">Project map</a><a href="https://github.com/ZetianYan/ConformalCovariantOperators" target="_blank">GitHub ↗</a></nav></header>

    <section className="frontier" id="home">
      <div className="frontierCopy"><p className="overline">A LEAN 4 FORMALIZATION PROJECT</p><h1>Conformal covariant<br/><em>operators.</em></h1><p className="lede">Explore the architecture of conformally covariant differential operators—from conformal foundations and ambient geometry to GJMS, Ovsienko–Redou, tree recurrence, and Juhl-type formulas.</p><div className="actions"><a href="#project-map" className="cta">Enter the project map <span>↓</span></a><a href="https://github.com/ZetianYan/ConformalCovariantOperators" target="_blank" className="ghost">View repository ↗</a></div></div>
      <div className="heroMath"><div className="orbit o1">FG</div><div className="orbit o2">PE</div><div className="orbit o3">OR</div><div className="mathCore"><b>P<sub>2k</sub></b><span>conformal covariance</span></div><p>e<sup>-(n/2+k)ω</sup> P<sub>2k</sub> e<sup>(n/2-k)ω</sup></p></div>
    </section>

    <section className="intro" id="introduction"><div><p className="overline">INTRODUCTION</p><h2>One formal library,<br/>six mathematical layers.</h2></div><div className="introText"><p>This repository formalizes higher-order extrinsic GJMS operators and the ambient, poly-GJMS, Ovsienko–Redou, tree-recurrence, Poincaré–Einstein, and Juhl-formula structures surrounding them.</p><p>The map below is the project’s actual README architecture. Every named source module is clickable and opens the corresponding Lean file without leaving the site.</p><div className="facts"><span><b>{total}</b> mapped Lean modules</span><span><b>5</b> top-level branches</span><span><b>Lean 4</b> + Mathlib</span></div></div></section>

    <section className="mapSection" id="project-map">
      <div className="mapHeader"><div><p className="overline">INTERACTIVE SOURCE ATLAS</p><h2>Project map</h2></div><p>Open any module as a paired mathematics–Lean workspace. Search by topic, author, declaration, file, or verification status.</p></div>
      <div className="branchLegend">{projectMap.children?.map(x => <a key={x.name} href={`#branch-${x.name}`}><b>{x.name}</b><span>{branchDescriptions[x.name]}</span><small>{countFiles(x)} files</small></a>)}</div>
      <div className="mapTools"><label><span>⌕</span><input value={query} onChange={e => setQuery(e.target.value)} placeholder="Search mathematics, authors, or Lean declarations…"/></label><span>{total} source modules · 9 primary references</span></div>
      {query.trim() ? <div className="results">{results.map((x) => <button key={x.file} onClick={() => openFile(x.file)}><b>{x.title}</b><span>{x.file}</span><small className={`statusBadge ${x.status}`}>{statusLabels[x.status]}</small><em>Open workspace →</em></button>)}{!results.length && <p>No module content matches “{query}”.</p>}</div> : <div className="mapCanvas"><ul className="rootTree"><TreeNode node={projectMap} depth={0} onOpen={openModule}/></ul></div>}
    </section>

    <section className="entryPoints"><p className="overline">REPOSITORY ENTRY POINTS</p><div>{["GJMSoperators/Tangentiality.lean","Ambient/FG.lean","Ambient/PE.lean","PolyGJMSoperators/Tree.lean","PolyGJMSoperators/OR.lean","Juhlformula/Juhlcombinatorics.lean"].map(file => <button key={file} onClick={() => openFile(file)}><span>import</span> ConformalCovariantOperators.{file.replaceAll("/",".").replace(".lean","")} <b>↗</b></button>)}</div></section>

    <footer><span>λ</span><p>Conformal Covariant Operators<br/><small>Developed by ZeTian Yan, Victor Xiao, and Tao Xu</small></p><a href="https://github.com/ZetianYan/ConformalCovariantOperators" target="_blank">Source on GitHub ↗</a></footer>

    {selected && <div className="viewerBackdrop" onMouseDown={closeModule}><section className="workbench" onMouseDown={e => e.stopPropagation()}>
      <header className="workbenchHead"><div><p>MODULE WORKBENCH</p><h3>{note?.title ?? selected.name}</h3><span>ConformalCovariantOperators/{selected.file}</span></div><div className="workbenchHeadActions">{note && <span className={`statusBadge ${note.status}`}>{statusLabels[note.status]}</span>}<a href={`https://github.com/ZetianYan/ConformalCovariantOperators/blob/main/ConformalCovariantOperators/${selected.file}`} target="_blank">GitHub ↗</a><button onClick={closeModule} aria-label="Close module workspace">×</button></div></header>
      <nav className="mobileTabs"><button className={mobileTab === "math" ? "active" : ""} onClick={() => setMobileTab("math")}>Mathematics</button><button className={mobileTab === "source" ? "active" : ""} onClick={() => setMobileTab("source")}>Lean source</button><button className={mobileTab === "refs" ? "active" : ""} onClick={() => setMobileTab("refs")}>References</button></nav>
      {loading ? <div className="workspaceLoading">Loading mathematics and Lean source…</div> : <div className="workbenchBody">
        <article className={`mathPanel ${mobileTab === "math" ? "mobileActive" : ""}`}>
          {note ? <>
            <div className="mathIntro"><p className="panelLabel">MATHEMATICAL PURPOSE</p><h4>{note.summary}</h4></div>
            {note.mathematicalContent.map((section) => <section className="mathSection" key={section.heading}><h5>{section.heading}</h5><p>{section.body}</p>{section.formula && <Formula value={section.formula}/>}</section>)}
            <section className="mathSection"><h5>Lean ↔ Mathematics</h5><div className="correspondenceTable">{note.correspondence.length ? note.correspondence.map((item) => <button key={`${item.leanDeclaration}-${item.line}`} onClick={() => jumpToLine(item.line)}><code>{item.leanDeclaration}</code><span>{item.mathematicalMeaning}</span><small>{item.kind} · line {item.line} →</small></button>) : <p>No top-level declarations were detected in this aggregate module.</p>}</div></section>
            <section className="dependencyGrid"><div><h5>Prerequisites</h5>{note.prerequisites.length ? note.prerequisites.map((file) => <button key={file} onClick={() => openFile(file)}>{file} ↗</button>) : <p>Foundational module</p>}</div><div><h5>Used by</h5>{note.usedBy.length ? note.usedBy.map((file) => <button key={file} onClick={() => openFile(file)}>{file} ↗</button>) : <p>No mapped direct importers</p>}</div></section>
            <section className="limitation"><h5>Status and limitation</h5><p>{note.limitations}</p></section>
          </> : <p>Mathematical note unavailable.</p>}
        </article>
        <article className={`referencePanel ${mobileTab === "refs" ? "mobileActive" : ""}`}>
          <p className="panelLabel">PRIMARY REFERENCES</p>
          {note?.references.map((moduleRef) => { const ref = referenceById.get(moduleRef.referenceId); return ref ? <section className="referenceCard" key={`${moduleRef.referenceId}-${moduleRef.locator}`}><span>{ref.year}</span><h4>{ref.title}</h4><p>{ref.authors}</p><b>{moduleRef.locator}</b><p>{moduleRef.note}</p><a href={ref.url} target="_blank">Open primary source ↗</a></section> : null; })}
          <p className="referenceCaution">Locators identify the mathematical source represented by this module; they do not claim a line-by-line translation unless the note explicitly says so.</p>
        </article>
        <article className={`codePanel ${mobileTab === "source" ? "mobileActive" : ""}`}>
          <div className="viewerBar"><span><i></i><i></i><i></i>{selected.file}</span><div><button onClick={() => navigator.clipboard.writeText(code)}>Copy source</button><a href={`https://github.com/ZetianYan/ConformalCovariantOperators/blob/main/ConformalCovariantOperators/${selected.file}`} target="_blank">GitHub ↗</a></div></div>
          <pre><code>{code.split(/\r?\n/).map((line, index) => <span className="codeLine" id={`code-line-${index + 1}`} key={index}><b>{index + 1}</b><em>{line || " "}</em></span>)}</code></pre>
        </article>
      </div>}
    </section></div>}
  </main>;
}
