import ConformalCovariantOperators.Ambient.PE.Basic

open Classical

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Defining functions and compactification

The differential nondegeneracy and gradient norm are certificate fields until
a manifold differential-calculus backend is connected.
-/

/-- A boundary defining function for a conformally compact bulk. -/
structure DefiningFunction (X : PESpace.{u, v}) where
  r : FunctionSymbol X.bulk
  positive_interior :
    forall x : X.bulk, x ∈ X.interior -> 0 < r x
  zero_on_boundary :
    forall x : X.boundary, r (X.boundaryInclusion x) = 0
  /-- The formal assertion that `dr` is nonzero along the boundary. -/
  nondegenerate_boundary : Prop

/-- The compactified metric `r^2 gPlus`. -/
def compactifiedMetric
    {X : PESpace}
    (gPlus : MetricSymbol X.bulk)
    (r : DefiningFunction X) :
    MetricSymbol X.bulk :=
  MetricSymbol.scaleByFunction (fun x => (r.r x) ^ 2) gPlus

/--
A geodesic defining function.

`normSqGradientCompactified` represents
`|dr|^2_(r^2 gPlus)`.  Its interpretation will be supplied by a concrete
Riemannian backend.
-/
structure GeodesicDefiningFunction
    (X : PESpace.{u, v})
    (gPlus : MetricSymbol X.bulk)
    extends DefiningFunction X where
  normSqGradientCompactified : FunctionSymbol X.bulk
  gradient_certificate :
    Prop
  geodesic_condition :
    forall x : X.bulk,
      x ∈ X.interior ->
      normSqGradientCompactified x = 1

namespace GeodesicDefiningFunction

variable {X : PESpace} {gPlus : MetricSymbol X.bulk}

@[simp]
theorem compactification
    (r : GeodesicDefiningFunction X gPlus) :
    compactifiedMetric gPlus r.toDefiningFunction
      =
    MetricSymbol.scaleByFunction (fun x => (r.r x) ^ 2) gPlus := by
  rfl

theorem normSqGradient_eq_one
    (r : GeodesicDefiningFunction X gPlus)
    {x : X.bulk}
    (hx : x ∈ X.interior) :
    r.normSqGradientCompactified x = 1 :=
  r.geodesic_condition x hx

end GeodesicDefiningFunction

end PE
end Ambient
end ConformalStructure
