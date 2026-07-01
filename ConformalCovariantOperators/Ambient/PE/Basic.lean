import ConformalCovariantOperators.Conformal.Basic

open Classical

noncomputable section

universe u v w

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Poincare-Einstein spaces

This file introduces the abstract objects used by the PE layer.  It does not
assume a manifold-with-boundary implementation.  Instead, `PESpace` records the
bulk, its conformal boundary, the dimension relation, and the two elementary
incidence predicates needed by defining functions.

`MetricSymbol` is deliberately syntax-level.  Concrete Riemannian backends can
interpret these expressions later without changing the PE interfaces.
-/

/-- Topological and dimensional data for a conformally compact bulk. -/
structure PESpace where
  /-- The compactified bulk type. -/
  bulk : Type u
  /-- The conformal boundary type. -/
  boundary : Type v
  /-- Dimension of the bulk. -/
  bulkDim : Nat
  /-- Dimension of the conformal boundary. -/
  boundaryDim : Nat
  /-- A PE bulk has one dimension more than its conformal boundary. -/
  dim_relation : bulkDim = boundaryDim + 1
  /-- The boundary inclusion into the compactified bulk. -/
  boundaryInclusion : boundary -> bulk
  /-- The predicate selecting interior bulk points. -/
  interior : Set bulk
  /-- Boundary points are not interior points. -/
  boundary_not_interior :
    forall x : boundary, boundaryInclusion x ∉ interior

namespace PESpace

@[simp]
theorem bulkDim_eq_boundaryDim_add_one (X : PESpace) :
    X.bulkDim = X.boundaryDim + 1 :=
  X.dim_relation

end PESpace

/-- A scalar function on a formal geometric carrier. -/
abbrev FunctionSymbol (X : Type u) := X -> Real

/--
Formal metric expressions.

Only the operations needed by conformal compactification, PE normal form, and
the cone decomposition are included at this stage.
-/
inductive MetricSymbol (X : Type u) where
  | zero : MetricSymbol X
  | atom : Nat -> MetricSymbol X
  | add : MetricSymbol X -> MetricSymbol X -> MetricSymbol X
  | scalarSMul : Real -> MetricSymbol X -> MetricSymbol X
  | functionSMul : FunctionSymbol X -> MetricSymbol X -> MetricSymbol X

namespace MetricSymbol

instance : Zero (MetricSymbol X) :=
  ⟨MetricSymbol.zero⟩

/-- Multiplication of a metric expression by a scalar function. -/
def scaleByFunction
    (a : FunctionSymbol X)
    (g : MetricSymbol X) :
    MetricSymbol X :=
  MetricSymbol.functionSMul a g

/-- Multiplication of a metric expression by a real scalar. -/
def scaleByScalar
    (a : Real)
    (g : MetricSymbol X) :
    MetricSymbol X :=
  MetricSymbol.scalarSMul a g

end MetricSymbol

/-- The conformal structure induced at infinity. -/
structure ConformalInfinity (X : PESpace.{u, v}) where
  boundaryConf : ConformalStructure.{v, w} X.boundary

/--
Abstract bulk metric data.

The Ricci tensor is supplied as a symbolic metric-type tensor.  The Einstein
equation is imposed in `EinsteinEquation.lean`.
-/
structure PEMetricData (X : PESpace.{u, v}) where
  conformalInfinity : ConformalInfinity.{u, v, w} X
  gPlus : MetricSymbol X.bulk
  ricci : MetricSymbol X.bulk

/-- The symbolic right-hand side `-n gPlus` of the PE Einstein equation. -/
def einsteinRHS
    (X : PESpace)
    (gPlus : MetricSymbol X.bulk) :
    MetricSymbol X.bulk :=
  MetricSymbol.scaleByScalar (-(X.boundaryDim : Real)) gPlus

end PE
end Ambient
end ConformalStructure
