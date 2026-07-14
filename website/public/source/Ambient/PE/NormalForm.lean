import ConformalCovariantOperators.Ambient.PE.DefiningFunction

open Classical

noncomputable section

universe u v w

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Poincare normal form

For a geodesic defining function, the PE metric has the symbolic form

`gPlus = r^(-2) (dr^2 + h_r)`.

The component realization is provided in `MetricComponents.lean`.
-/

/-- Symbolic Poincare normal-form data. -/
structure PoincareNormalFormData (X : PESpace.{u, v}) where
  metric : PEMetricData.{u, v, w} X
  r : GeodesicDefiningFunction X metric.gPlus
  /-- The boundary representative `h = h_0`. -/
  h0 : MetricSymbol X.boundary
  /-- The one-parameter family `h_r`. -/
  hR : Real -> MetricSymbol X.boundary
  hR_zero : hR 0 = h0
  /-- The formal `dr^2` term on the compactified bulk. -/
  drSquared : MetricSymbol X.bulk
  /-- The family `h_r`, pulled back to the bulk collar. -/
  sliceMetric : MetricSymbol X.bulk
  /-- Compatibility of `sliceMetric` with `hR` in a collar chart. -/
  sliceMetric_certificate : Prop
  /-- Compatibility of `h0` with the chosen conformal infinity. -/
  boundary_metric_certificate : Prop
  /-- The Poincare normal-form identity. -/
  gPlus_normal_form :
    metric.gPlus
      =
    MetricSymbol.scaleByFunction
      (fun x => ((r.r x) ^ 2)⁻¹)
      (MetricSymbol.add drSquared sliceMetric)

namespace PoincareNormalFormData

variable {X : PESpace} (NF : PoincareNormalFormData X)

@[simp]
theorem hR_at_zero :
    NF.hR 0 = NF.h0 :=
  NF.hR_zero

/-- The identity `gPlus = r^(-2) (dr^2 + h_r)`. -/
theorem gPlus_eq_normalForm :
    NF.metric.gPlus
      =
    MetricSymbol.scaleByFunction
      (fun x => ((NF.r.r x) ^ 2)⁻¹)
      (MetricSymbol.add NF.drSquared NF.sliceMetric) :=
  NF.gPlus_normal_form

end PoincareNormalFormData

end PE
end Ambient
end ConformalStructure
