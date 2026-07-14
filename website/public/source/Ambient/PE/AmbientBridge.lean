import ConformalCovariantOperators.Ambient.FG.NormalForm
import ConformalCovariantOperators.Ambient.PE.EinsteinEquation

open Classical

noncomputable section

universe u v w x y

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Ambient--PE bridge

The coordinate change is

`rho = -r^2 / 2`, `s = r t`,

and the slice metrics satisfy `h_r = g_(-r^2/2)`.  In these coordinates the
ambient metric has the cone decomposition

`gAmbient = -ds^2 + s^2 gPlus`.

At the current abstraction level, metric transport and the final decomposition
are certificate fields.  The coordinate identities themselves are definitions.
-/

/-- The ambient normal coordinate corresponding to a PE radius. -/
def ambientRhoOfRadial (r : Real) : Real :=
  -(r ^ 2) / 2

/-- The cone scale coordinate `s = r t`. -/
def coneScale (r t : Real) : Real :=
  r * t

@[simp]
theorem ambientRhoOfRadial_zero :
    ambientRhoOfRadial 0 = 0 := by
  norm_num [ambientRhoOfRadial]

@[simp]
theorem coneScale_eq_mul (r t : Real) :
    coneScale r t = r * t := by
  rfl

/-- Data identifying an FG normal form with a PE normal form. -/
structure AmbientPEBridge
    {M : Type u}
    {Conf : ConformalStructure.{u, v} M}
    (A : FG.NormalAmbientData Conf)
    {X : PESpace.{w, x}}
    (NF : PoincareNormalFormData.{w, x, y} X) where
  /-- Identification of the conformal boundary with the FG base. -/
  boundaryEquiv : X.boundary ≃ M
  /-- Adapter from concrete FG metric fields to PE metric symbols. -/
  boundaryMetricAdapter :
    Conf.MetricField -> MetricSymbol X.boundary
  /-- The relation `h_r = g_(-r^2/2)`. -/
  hR_eq :
    forall r : Real,
      NF.hR r
        =
      boundaryMetricAdapter (A.gRho (ambientRhoOfRadial r))
  /-- Ambient scale coordinate `t` on the PE collar. -/
  ambientT : FunctionSymbol X.bulk
  /-- Ambient normal coordinate `rho` on the PE collar. -/
  ambientRho : FunctionSymbol X.bulk
  /-- Cone coordinate `s`. -/
  s : FunctionSymbol X.bulk
  rho_coordinate_eq :
    forall z : X.bulk,
      ambientRho z = ambientRhoOfRadial (NF.r.r z)
  s_coordinate_eq :
    forall z : X.bulk,
      s z = coneScale (NF.r.r z) (ambientT z)
  /-- The formal `ds^2` metric expression. -/
  dsSquared : MetricSymbol X.bulk
  /-- The ambient metric transported to cone coordinates. -/
  ambientMetricInConeCoordinates : MetricSymbol X.bulk
  /-- Certificate for `gAmbient = -ds^2 + s^2 gPlus`. -/
  cone_decomposition :
    ambientMetricInConeCoordinates
      =
    MetricSymbol.add
      (MetricSymbol.scaleByScalar (-1) dsSquared)
      (MetricSymbol.scaleByFunction (fun z => (s z) ^ 2) NF.metric.gPlus)

namespace AmbientPEBridge

variable
    {M : Type u}
    {Conf : ConformalStructure.{u, v} M}
    {A : FG.NormalAmbientData Conf}
    {X : PESpace.{w, x}}
    {NF : PoincareNormalFormData.{w, x, y} X}

/-- The slice relation `h_r = g_(-r^2/2)`. -/
theorem boundary_family_from_ambient
    (B : AmbientPEBridge A NF)
    (r : Real) :
    NF.hR r
      =
    B.boundaryMetricAdapter (A.gRho (ambientRhoOfRadial r)) :=
  B.hR_eq r

/-- The ambient metric cone decomposition `-ds^2 + s^2 gPlus`. -/
theorem ambient_metric_cone_decomposition
    (B : AmbientPEBridge A NF) :
    B.ambientMetricInConeCoordinates
      =
    MetricSymbol.add
      (MetricSymbol.scaleByScalar (-1) B.dsSquared)
      (MetricSymbol.scaleByFunction (fun z => (B.s z) ^ 2) NF.metric.gPlus) :=
  B.cone_decomposition

end AmbientPEBridge

end PE
end Ambient
end ConformalStructure
