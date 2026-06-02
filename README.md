# Higher Order Extrinsic GJMS Operators

This repository is a Lean 4 formalization project for higher-order extrinsic
GJMS operators and related ambient, poly-GJMS, Ovsienko-Redou, and Juhl-type
formula structures.

The project is being developed by ZeTian Yan and Victor Xiao.

## Project Map

```mermaid
mindmap
  root((ExtrinsicGJMSOperators))
    Geometry
      Conformal
        Basic
        Density
      Ambient
        Ambientbasic
        Ambientdensity
        Ambientoperator
        Ambienttangential
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

The files under `Geometry/Conformal` and `Geometry/Ambient` provide the formal
background objects used by the operator constructions:

- conformal structures and densities;
- formal ambient bundles and straight-form ambient data;
- ambient scalar functions, ambient Laplacian powers, homogeneity, and `Q`-mod
  tangentiality;
- weighted tangential ambient operators.

These files are the base layer for both the GJMS and poly-GJMS developments.

### 2. GJMS Operators

The `Geometry/GJMSoperators` directory packages powers of the ambient Laplacian
as abstract GJMS-type operators.

Important interfaces include:

- `GJMS.AbstractOperator`;
- `GJMS.Family`;
- `GJMS.canonicalAmbientGJMS`;
- `GJMS.canonicalAmbientGJMSFamily`;
- tangentiality of ambient Laplacian powers at the critical GJMS weights.

This layer supplies the canonical operator family used by the Juhl composition
side.

### 3. Poly-GJMS and Ovsienko-Redou Side

The `Geometry/PolyGJMSoperators` directory develops the poly-laplacian and
Ovsienko-Redou formalism.

The main ingredients are:

- poly-GJMS operator syntax and homogeneity bookkeeping;
- Laplacian words and linear combinations;
- OR index data;
- OR coefficient recurrence and closed formulas;
- closed OR operators.

This is the side that will eventually be connected to the Juhl formula bridge.

### 4. Juhl Formula: Composition Side

The `Geometry/Juhlformula/Juhloperators` directory formalizes the ordered
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

### 5. Juhl Formula: Formal Obstruction Side

The `Geometry/Juhlformula/Juhlcombinatorics` directory formalizes the
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

## Build Instructions

This project uses Lean 4 with Lake and Mathlib.

To build the default executable target:

```bash
lake build
```

To build the current Juhl formula scaffold:

```bash
lake build ExtrinsicGJMSOperators.Geometry.Juhlformula.Juhlcombinatorics
```

To check exported Juhl interfaces interactively:

```lean
import ExtrinsicGJMSOperators.Geometry.Juhlformula.Juhlcombinatorics

#check ConformalStructure.Ambient.Operators.Calculus.Juhl.FormalExpr
#check ConformalStructure.Ambient.Operators.Calculus.Juhl.formalP
#check ConformalStructure.Ambient.Operators.Calculus.Juhl.CurvedORJuhlTypeFormula
```

## Current Status

Implemented:

- ambient formal calculus and tangentiality framework;
- abstract and canonical GJMS operators;
- poly-GJMS and OR coefficient infrastructure;
- Juhl ordered composition syntax;
- formal obstruction recursion syntax;
- low-order formal checks for raw `P_2` and `P_4`;
- abstract formal statement, OR bridge, and final curved OR Juhl-type formula
  pipeline.

Next natural steps:

- replace placeholder Juhl coefficient functions by the chosen closed product
  formulas;
- enumerate ordered compositions of `N` in a computable way;
- build `FormalJuhlRHS` values from actual composition data;
- connect existing OR index/operator data to `ORFormalizationData`;
- prove coefficient compatibility between the OR and Juhl sides;
- replace identity bridges in low order with genuine OR bridges.

## Repository Entry Points

Useful imports:

```lean
import ExtrinsicGJMSOperators.Geometry.GJMSoperators.Tangentiality
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OR
import ExtrinsicGJMSOperators.Geometry.Juhlformula.Juhlcombinatorics
```

