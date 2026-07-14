import ConformalCovariantOperators.Ambient.PE.NormalForm
import ConformalCovariantOperators.Ambient.PE.Renormalization.CutoffFunctional

open Classical

noncomputable section

universe u v w z

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Renormalized curvature integrals

The invariant type is a parameter so that Phase C can insert its eventual
`ScalarRiemannianInvariant` without changing the renormalization layer.
-/

/-- Cutoff-integral data for a chosen invariant on a PE normal form. -/
structure CurvatureIntegralCutoffData
    (X : PESpace.{u, v})
    {Invariant : Type z}
    (I : Invariant) where
  normalForm : PoincareNormalFormData.{u, v, w} X
  cutoffIntegral : PosReal -> Real
  cutoffExpansion : LaurentLogExpansion Real

/-- Curvature integration as a generic cutoff functional. -/
def curvatureIntegralCutoffFunctional
    (X : PESpace.{u, v})
    {Invariant : Type z}
    (I : Invariant) :
    CutoffFunctional
      (CurvatureIntegralCutoffData.{u, v, w, z} X I)
      Real where
  cutoffValue := fun D => D.cutoffIntegral
  expansion := fun D => D.cutoffExpansion

/-- The renormalized integral of a chosen curvature invariant. -/
def RenormalizedCurvatureIntegral
    {X : PESpace}
    {Invariant : Type z}
    {I : Invariant}
    (D : CurvatureIntegralCutoffData X I) :
    Real :=
  (curvatureIntegralCutoffFunctional X I).renormalizedValue D

/-- The logarithmic anomaly of a curvature integral. -/
def CurvatureIntegralAnomaly
    {X : PESpace}
    {Invariant : Type z}
    {I : Invariant}
    (D : CurvatureIntegralCutoffData X I) :
    Real :=
  (curvatureIntegralCutoffFunctional X I).anomalyValue D

@[simp]
theorem RenormalizedCurvatureIntegral_eq_finitePart
    {X : PESpace}
    {Invariant : Type z}
    {I : Invariant}
    (D : CurvatureIntegralCutoffData X I) :
    RenormalizedCurvatureIntegral D = finitePart D.cutoffExpansion := by
  rfl

@[simp]
theorem CurvatureIntegralAnomaly_eq_logAnomaly
    {X : PESpace}
    {Invariant : Type z}
    {I : Invariant}
    (D : CurvatureIntegralCutoffData X I) :
    CurvatureIntegralAnomaly D = logAnomaly D.cutoffExpansion := by
  rfl

end PE
end Ambient
end ConformalStructure
