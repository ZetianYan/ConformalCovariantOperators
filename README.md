# Conformal Covariant Operators

This repository is a Lean 4 formalization project for conformally covariant
differential operators, including higher-order extrinsic GJMS operators and
related ambient, poly-GJMS, Ovsienko-Redou, tree-recurrence, and Juhl-type
formula structures.

The project is being developed by ZeTian Yan and Victor Xiao.

## Project Map

```mermaid
mindmap
  root((ConformalCovariantOperators))
    Conformal
      Basic
      Density
    Ambient
      Ambientbasic
      Ambientdensity
      Ambientoperator
      Ambienttangential
      FG
        Index
        NormalForm
        InverseMetric
        Christoffel
        Laplacian
        Commutators
        CalculusInstance
        RicciNormalForm
        FormalJets
        Recursion
        Obstruction
      PE
        Basic
        DefiningFunction
        NormalForm
        MetricComponents
        EinsteinEquation
        AmbientBridge
        Invariants
          RiemannianInvariant
          Straightenable
          LaplacianRecursion
          NaturalDivergence
          Pfaffian
        Renormalization
          LaurentLogExpansion
          FinitePart
          CutoffFunctional
          Volume
          CurvatureIntegral
          DivergenceVanishing
        Applications
          CaseKhaitanLinTyrrellYuan
          PfaffianApplication
    GJMSoperators
      Basic
      Ambientconstruction
      Tangentiality
    PolyGJMSoperators
      Basic
      Homogeneity
      Operators
      Boundary
      Tangential
      Bidifferential
      LaplacianWords
      Tree
        TreeLaplacianWords
        TreeRecurrence
        TreeDefectCancellation
        TreeChainComplex
      LinearCombination
      PolyLaplacianCombination
      OvsienkoRedou
      OR
        Index
        OperatorData
        DefectCancellation
        ClosedOperator
        Coefficients
          Parameters
          Combinatorics
          Recurrence
          RatioLemmas
          ClosedFormula
          ClosedSatisfiesRecurrence
    Juhlformula
      Juhloperators
        Basic
        Composition
        GJMSComposition
        Coefficients
      Juhlcombinatorics
        FormalJets
        Recursion
        LowOrderCheck
        FormalStatement
        ORBridge
        CurvedORJuhlFormula
```

## Mathematical Layers

### 1. Conformal and Ambient Foundations

The files under `Conformal` and `Ambient` provide the formal
background objects used by the operator constructions:

- conformal structures and densities;
- formal ambient bundles and straight-form ambient data;
- Fefferman-Graham straight normal-form component calculus, including ambient
  indices, metric components, inverse metric components, Christoffel symbols,
  normal-form `Q = 2 rho t^2`, commutator identities, and a bridge to
  `Calculus.AlgebraicIdentities`;
- Fefferman-Graham Ricci normal-form equations, finite formal metric jets,
  finite-order recursion scaffolding, and even-dimensional obstruction data;
- Poincare-Einstein spaces, defining functions, geodesic compactifications,
  Poincare normal form, metric and inverse-metric components, Einstein
  expansion certificates, and the FG--PE cone bridge;
- common Laurent/log expansions, parity predicates, finite parts, logarithmic
  anomalies, generic cutoff functionals, renormalized volume, and renormalized
  curvature integrals;
- ambient scalar functions, ambient Laplacian powers, homogeneity, and `Q`-mod
  tangentiality;
- weighted tangential ambient operators.

These files are the base layer for both the GJMS and poly-GJMS developments.

### 2. PE Renormalized Curvature Integrals

The `Ambient/PE/Invariants` and `Ambient/PE/Applications` directories formalize
the theorem mechanism in Case--Khaitan--Lin--Tyrrell--Yuan:

- symbolic tensor invariants with rank, weight, tensor weight, and parity;
- straightenable invariants relative to an explicit evaluation model;
- closure under tensor products and contractions;
- Proposition 3.7's ambient Laplacian recursion, proved by induction;
- natural divergences and the Proposition 3.10 cone-rule interface;
- a `PERenormalizationPackage` connected to Phase B finite parts;
- Lemma 4.1's weighted divergence-vanishing interface;
- the formal Theorem 1.4 finite-part identity;
- Pfaffian-like invariants, `P_l_n`, and a formal Theorem 1.1 assembly.

In the paper, `n` is the dimension of the PE manifold, so the Lean
formalization uses `PESpace.bulkDim`. The expression
`restrictToEinsteinSlice` represents the pullback `i^*` from a canonical
ambient space to the Einstein PE manifold. The right-hand side of Theorem 1.4
is an ordinary convergent integral on that PE manifold, not an integral on its
conformal boundary.

The geometric and analytic inputs not yet derived from a concrete tensor
backend are exposed as named model laws and certificates. The iteration,
weight bookkeeping, coefficient inversion, finite-part bridge, and final
theorem assembly are proved in Lean.

### 3. GJMS Operators

The `GJMSoperators` directory packages powers of the ambient Laplacian
as abstract GJMS-type operators.

Important interfaces include:

- `GJMS.AbstractOperator`;
- `GJMS.Family`;
- `GJMS.canonicalAmbientGJMS`;
- `GJMS.canonicalAmbientGJMSFamily`;
- tangentiality of ambient Laplacian powers at the critical GJMS weights.

This layer supplies the canonical operator family used by the Juhl composition
side.

### 4. Poly-GJMS and Ovsienko-Redou Side

The `PolyGJMSoperators` directory develops the poly-laplacian and
Ovsienko-Redou formalism.

The main ingredients are:

- poly-GJMS operator syntax and homogeneity bookkeeping;
- Laplacian words and linear combinations;
- rank-general left-comb tree Laplacian words for nested multilinear
  Case--Cieslak-type operators;
- path-wise recurrence data for slot-wise `Q`-commutator defect cancellation;
- OR index data;
- OR coefficient recurrence and closed formulas;
- closed OR operators.

This is the side that will eventually be connected to the Juhl formula bridge.

The current tree-word layer lives in:

- `TreeLaplacianWords.lean`: `CombIndex r k`, `PolyTreeIndex`, and the
  left-comb nested word operator `CombIndex.toOperator`;
- `TreeRecurrence.lean`: `pathToRoot`, `descendants`, `subtreeWeight`,
  `defectCoeff`, `pathDefectCoeff`, `RankRecurrence`, and `dOne`;
- `TreeDefectCancellation.lean`: an abstract
  `RecurrenceImpliesTangentiality` interface saying that the path-wise
  recurrence cancels the slot-wise defects and implies tangentiality;
- `TreeChainComplex.lean`: first-kernel and Euler-characteristic targets for
  the rank-general recurrence complex;
- `Tree.lean`: aggregate import for the tree-word layer.

This layer intentionally does not include formal self-adjointness. It focuses
only on the general rank `(r+1)` tangentiality and recurrence side.

### 5. Juhl Formula: Composition Side

The `Juhlformula/Juhloperators` directory formalizes the ordered
composition side of Juhl-type formulas.

Current files:

- `Basic.lean`: ordered compositions `Composition N`;
- `Composition.lean`: composition of abstract GJMS operators;
- `GJMSComposition.lean`: specialization to the canonical ambient GJMS family;
- `Coefficients.lean`: abstract and placeholder closed coefficient systems.

This layer models expressions of the form

```text
P_{2I} = P_{2I_1} o ... o P_{2I_r}.
```

### 6. Juhl Formula: Formal Obstruction Side

The `Juhlformula/Juhlcombinatorics` directory formalizes the
syntax-level obstruction recursion.

Current files:

- `FormalJets.lean`: formal expression syntax, Taylor denominators, and
  coefficients `L_m`;
- `Recursion.lean`: formal recursive elimination of normal jets and definition
  of `formalP`;
- `LowOrderCheck.lean`: raw low-order checks for `P_2` and `P_4`;
- `FormalStatement.lean`: statement layer for `formalP N = Juhl RHS`;
- `ORBridge.lean`: abstract bridge between Juhl RHS and OR RHS;
- `CurvedORJuhlFormula.lean`: final assembly layer
  `formalP N = OR RHS`.

This side is intentionally independent of `CalConf`, `Function Conf`, and
concrete ambient operators. It is a pure formal algebra layer designed to be
connected later to the curved operator side.

## Juhl Pipeline

```mermaid
flowchart TD
    A["Composition N"] --> B["composeGJMS"]
    B --> C["canonicalGJMSComposition"]
    D["FormalExpr"] --> E["Lcoeff ell m"]
    E --> F["solvedJet ell m"]
    F --> G["obstructionCoeff ell"]
    G --> H["formalP ell"]
    H --> I["FormalJuhlStatement"]
    C --> I
    I --> J["ORBridge"]
    J --> K["CurvedORJuhlTypeFormula"]
```

The current formal Juhl pipeline is deliberately split into two sides:

- composition side: ordered GJMS compositions and coefficients;
- obstruction side: formal jets, recursion, and low-order checks.

The final bridge is currently abstract. This keeps the project compiling while
the exact OR-to-Juhl coefficient and operator compatibility theorems are added
incrementally.

## Rank-General Tree Pipeline

```mermaid
flowchart TD
    A["CombIndex r k"] --> B["left-comb nested word"]
    B --> C["CombIndex.toOperator"]
    A --> D["addAt: beta + e_v"]
    D --> E["defectCoeff C_v(beta)"]
    E --> F["pathDefectCoeff B_j(beta)"]
    F --> G["RankRecurrence"]
    G --> H["dOne / first kernel"]
    G --> I["RecurrenceImpliesTangentiality"]
    I --> J["weighted multi-tangential operator"]
```

For `r = 3`, the left-comb word specializes to the Case--Cieslak-type
tridifferential shape

```text
Delta^a0 (Delta^a1 ((Delta^a2 u0) * (Delta^a3 u1)) * Delta^a4 u2).
```

For general `r`, the same syntax gives a rank `(r+1)` framework with `r`
input functions and `2r - 1` vertex powers.

## Build Instructions

This project uses Lean 4 with Lake and Mathlib.

To build the default executable target:

```bash
lake build
```

To build the current Juhl formula scaffold:

```bash
lake build ConformalCovariantOperators.Juhlformula.Juhlcombinatorics
```

To build the rank-general left-comb tree formalization:

```bash
lake build ConformalCovariantOperators.PolyGJMSoperators.Tree
```

To build the Fefferman-Graham normal-form scaffold:

```bash
lake build ConformalCovariantOperators.Ambient.FG
```

To build the Poincare-Einstein geometry and renormalization layers:

```bash
lake build ConformalCovariantOperators.Ambient.PE
```

To build only the Phase B renormalization layer:

```bash
lake build ConformalCovariantOperators.Ambient.PE.Renormalization
```

To build the Case paper main line and Pfaffian application:

```bash
lake build ConformalCovariantOperators.Ambient.PE.Applications
```

Its main exported interfaces are:

```lean
import ConformalCovariantOperators.Ambient.PE

#check ConformalStructure.Ambient.PE.PESpace
#check ConformalStructure.Ambient.PE.DefiningFunction
#check ConformalStructure.Ambient.PE.GeodesicDefiningFunction
#check ConformalStructure.Ambient.PE.PoincareNormalFormData
#check ConformalStructure.Ambient.PE.gPlusUp_mul_gPlusDown
#check ConformalStructure.Ambient.PE.IsPoincareEinstein
#check ConformalStructure.Ambient.PE.AmbientPEBridge
#check ConformalStructure.Ambient.PE.AmbientPEBridge.ambient_metric_cone_decomposition
#check ConformalStructure.Ambient.PE.LaurentLogExpansion
#check ConformalStructure.Ambient.PE.finitePart
#check ConformalStructure.Ambient.PE.logAnomaly
#check ConformalStructure.Ambient.PE.CutoffFunctional
#check ConformalStructure.Ambient.PE.renormalizedValue
#check ConformalStructure.Ambient.PE.RenormalizableGeometricObject
#check ConformalStructure.Ambient.PE.RenormalizedVolume
#check ConformalStructure.Ambient.PE.RenormalizedCurvatureIntegral
#check ConformalStructure.Ambient.PE.TensorInvariant
#check ConformalStructure.Ambient.PE.Straightenable
#check ConformalStructure.Ambient.PE.CaseLaplacianRecursion
#check ConformalStructure.Ambient.PE.straightenable_laplacian_iterate
#check ConformalStructure.Ambient.PE.PERenormalizationPackage
#check ConformalStructure.Ambient.PE.theorem_1_4_formal
#check ConformalStructure.Ambient.PE.P_l_n
#check ConformalStructure.Ambient.PE.renormalizedIntegral_WeylPfLike
#check ConformalStructure.Ambient.PE.theorem_1_1_formal
```

To check exported Juhl interfaces interactively:

```lean
import ConformalCovariantOperators.Juhlformula.Juhlcombinatorics

#check ConformalStructure.Ambient.Operators.Calculus.Juhl.FormalExpr
#check ConformalStructure.Ambient.Operators.Calculus.Juhl.formalP
#check ConformalStructure.Ambient.Operators.Calculus.Juhl.CurvedORJuhlTypeFormula
```

To check exported tree-word interfaces interactively:

```lean
import ConformalCovariantOperators.PolyGJMSoperators.Tree

#check ConformalStructure.Ambient.Operators.Calculus.CombIndex
#check ConformalStructure.Ambient.Operators.Calculus.CombIndex.toOperator
#check ConformalStructure.Ambient.Operators.Calculus.LeftComb.RankRecurrence
#check ConformalStructure.Ambient.Operators.Calculus.LeftComb.recurrence_implies_tangential
```

## Current Status

Implemented:

- ambient formal calculus and tangentiality framework;
- Fefferman-Graham straight normal-form scaffold and
  `FG_algebraicIdentities` bridge into the existing ambient calculus;
- Fefferman-Graham Ricci normal-form symbolic equations, formal metric jets,
  finite recursion wrappers, and obstruction tensor scaffold;
- Poincare-Einstein Phase A, including the abstract conformal compactification,
  geodesic defining functions, symbolic and component normal forms, the full
  component inverse identity, Einstein/parity certificates, and the ambient
  cone decomposition interface;
- Poincare-Einstein Phase B, including finite Laurent/log expansions, generic
  finite-part cutoff functionals, and their volume and curvature-integral
  instances;
- Poincare-Einstein Phase C for the Case--Khaitan--Lin--Tyrrell--Yuan paper,
  including symbolic invariant calculus, straightenable closure, Proposition
  3.7 recursion, natural-divergence and Lemma 4.1 interfaces, the formal
  Theorem 1.4, and the Pfaffian application scaffold;
- abstract and canonical GJMS operators;
- poly-GJMS and OR coefficient infrastructure;
- rank-general left-comb tree Laplacian word syntax;
- path-wise recurrence and first-differential interfaces for general rank
  `(r+1)` tangentiality;
- Juhl ordered composition syntax;
- formal obstruction recursion syntax;
- low-order formal checks for raw `P_2` and `P_4`;
- abstract formal statement, OR bridge, and final curved OR Juhl-type formula
  pipeline.

Next natural steps:

- instantiate `InvariantEvaluationModel` from a concrete tensor evaluator;
- derive `EinsteinAmbientLaplacianFormula` from the existing ambient calculus;
- prove the Lemma 4.1 package fields from PE parity expansions;
- implement Proposition 3.8's corrected-divergence recursion;
- derive the Pfaffian reduction certificate term by term from Theorem 1.4;
- add the low-order `Pf_2`, `Pf_3`, and `Pf_4` contraction formulas;
- replace placeholder Juhl coefficient functions by the chosen closed product
  formulas;
- enumerate ordered compositions of `N` in a computable way;
- build `FormalJuhlRHS` values from actual composition data;
- prove the concrete left-comb commutator defect formula;
- instantiate `RecurrenceImpliesTangentiality` from the commutator formula;
- extend from left-comb trees to arbitrary rooted binary trees;
- develop higher differentials and generic exactness for the tree recurrence
  complex;
- connect existing OR index/operator data to `ORFormalizationData`;
- prove coefficient compatibility between the OR and Juhl sides;
- replace identity bridges in low order with genuine OR bridges.

## Repository Entry Points

Useful imports:

```lean
import ConformalCovariantOperators.GJMSoperators.Tangentiality
import ConformalCovariantOperators.Ambient.FG
import ConformalCovariantOperators.Ambient.PE
import ConformalCovariantOperators.PolyGJMSoperators.Tree
import ConformalCovariantOperators.PolyGJMSoperators.OR
import ConformalCovariantOperators.Juhlformula.Juhlcombinatorics
```
