"use client";

import { useEffect, useMemo, useState } from "react";

type MapNode = { name: string; file?: string; children?: MapNode[] };

const projectMap: MapNode = { name: "ConformalCovariantOperators", file: "README.md", children: [
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
  const [loading, setLoading] = useState(false);
  const [query, setQuery] = useState("");
  const total = useMemo(() => countFiles(projectMap), []);

  useEffect(() => {
    if (!selected?.file) return;
    setLoading(true); setCode("");
    fetch(`/source/${selected.file}`).then(r => r.text()).then(setCode).catch(() => setCode("Unable to load this source file.")).finally(() => setLoading(false));
  }, [selected]);

  function find(node: MapNode): MapNode[] { const own = node.name.toLowerCase().includes(query.toLowerCase()) ? [node] : []; return [...own, ...(node.children?.flatMap(find) ?? [])]; }
  const results = query.trim() ? find(projectMap).filter(x => x.file) : [];

  return <main>
    <header className="nav"><a href="#home" className="wordmark"><span>λ</span><b>Conformal Covariant Operators</b></a><nav><a href="#introduction">Introduction</a><a href="#project-map">Project map</a><a href="https://github.com/ZetianYan/ConformalCovariantOperators" target="_blank">GitHub ↗</a></nav></header>

    <section className="frontier" id="home">
      <div className="frontierCopy"><p className="overline">A LEAN 4 FORMALIZATION PROJECT</p><h1>Conformal covariant<br/><em>operators.</em></h1><p className="lede">Explore the architecture of conformally covariant differential operators—from conformal foundations and ambient geometry to GJMS, Ovsienko–Redou, tree recurrence, and Juhl-type formulas.</p><div className="actions"><a href="#project-map" className="cta">Enter the project map <span>↓</span></a><a href="https://github.com/ZetianYan/ConformalCovariantOperators" target="_blank" className="ghost">View repository ↗</a></div></div>
      <div className="heroMath"><div className="orbit o1">FG</div><div className="orbit o2">PE</div><div className="orbit o3">OR</div><div className="mathCore"><b>P<sub>2k</sub></b><span>conformal covariance</span></div><p>e<sup>-(n/2+k)ω</sup> P<sub>2k</sub> e<sup>(n/2-k)ω</sup></p></div>
    </section>

    <section className="intro" id="introduction"><div><p className="overline">INTRODUCTION</p><h2>One formal library,<br/>six mathematical layers.</h2></div><div className="introText"><p>This repository formalizes higher-order extrinsic GJMS operators and the ambient, poly-GJMS, Ovsienko–Redou, tree-recurrence, Poincaré–Einstein, and Juhl-formula structures surrounding them.</p><p>The map below is the project’s actual README architecture. Every named source module is clickable and opens the corresponding Lean file without leaving the site.</p><div className="facts"><span><b>{total}</b> mapped Lean modules</span><span><b>5</b> top-level branches</span><span><b>Lean 4</b> + Mathlib</span></div></div></section>

    <section className="mapSection" id="project-map">
      <div className="mapHeader"><div><p className="overline">INTERACTIVE SOURCE ATLAS</p><h2>Project map</h2></div><p>Follow the README hierarchy. Click any <b>LEAN</b> node to inspect its real source; use + / − to navigate large branches.</p></div>
      <div className="branchLegend">{projectMap.children?.map(x => <a key={x.name} href={`#branch-${x.name}`}><b>{x.name}</b><span>{branchDescriptions[x.name]}</span><small>{countFiles(x)} files</small></a>)}</div>
      <div className="mapTools"><label><span>⌕</span><input value={query} onChange={e => setQuery(e.target.value)} placeholder="Find a module…"/></label><span>{total} source modules mapped</span></div>
      {query.trim() ? <div className="results">{results.map((x,i) => <button key={`${x.file}-${i}`} onClick={() => setSelected(x)}><b>{x.name}</b><span>{x.file}</span><em>Open source →</em></button>)}{!results.length && <p>No source module matches “{query}”.</p>}</div> : <div className="mapCanvas"><ul className="rootTree"><TreeNode node={projectMap} depth={0} onOpen={setSelected}/></ul></div>}
    </section>

    <section className="entryPoints"><p className="overline">REPOSITORY ENTRY POINTS</p><div>{["GJMSoperators/Tangentiality.lean","Ambient/FG.lean","Ambient/PE.lean","PolyGJMSoperators/Tree.lean","PolyGJMSoperators/OR.lean","Juhlformula/Juhlcombinatorics.lean"].map(file => <button key={file} onClick={() => setSelected({name:file.split("/").at(-1)!.replace(".lean",""),file})}><span>import</span> ConformalCovariantOperators.{file.replaceAll("/",".").replace(".lean","")} <b>↗</b></button>)}</div></section>

    <footer><span>λ</span><p>Conformal Covariant Operators<br/><small>Developed by ZeTian Yan, Victor Xiao, and Tao Xu</small></p><a href="https://github.com/ZetianYan/ConformalCovariantOperators" target="_blank">Source on GitHub ↗</a></footer>

    {selected && <div className="viewerBackdrop" onMouseDown={() => setSelected(null)}><aside className="viewer" onMouseDown={e => e.stopPropagation()}>
      <div className="viewerHead"><div><p>LEAN SOURCE</p><h3>{selected.name}</h3><span>ConformalCovariantOperators/{selected.file}</span></div><button onClick={() => setSelected(null)} aria-label="Close source">×</button></div>
      <div className="viewerBar"><span><i></i><i></i><i></i>{selected.file}</span><div><button onClick={() => navigator.clipboard.writeText(code)}>Copy</button><a href={`https://github.com/ZetianYan/ConformalCovariantOperators/blob/main/ConformalCovariantOperators/${selected.file}`} target="_blank">GitHub ↗</a></div></div>
      <pre className={loading ? "loading" : ""}><code>{loading ? "Loading Lean source…" : code}</code></pre>
    </aside></div>}
  </main>;
}
