import ConformalCovariantOperators.Ambient.PE.NormalForm
import ConformalCovariantOperators.Ambient.PE.Renormalization.CutoffFunctional

open Classical

noncomputable section

universe u v w

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Renormalized volume

The analytic construction of the cutoff volume is external data in Phase B.
Its renormalized value is the common finite-part operation.
-/

/-- Cutoff-volume data for one PE normal form. -/
structure PEVolumeCutoffData (X : PESpace.{u, v}) where
  normalForm : PoincareNormalFormData.{u, v, w} X
  cutoffVolume : PosReal -> Real
  volumeExpansion : LaurentLogExpansion Real

/-- Volume as an instance of the generic cutoff-functional interface. -/
def volumeCutoffFunctional
    (X : PESpace.{u, v}) :
    CutoffFunctional (PEVolumeCutoffData.{u, v, w} X) Real where
  cutoffValue := fun D => D.cutoffVolume
  expansion := fun D => D.volumeExpansion

/-- The renormalized volume, defined as the constant Laurent coefficient. -/
def RenormalizedVolume
    {X : PESpace}
    (D : PEVolumeCutoffData X) :
    Real :=
  (volumeCutoffFunctional X).renormalizedValue D

/-- The logarithmic volume anomaly. -/
def VolumeAnomaly
    {X : PESpace}
    (D : PEVolumeCutoffData X) :
    Real :=
  (volumeCutoffFunctional X).anomalyValue D

@[simp]
theorem RenormalizedVolume_eq_finitePart
    {X : PESpace}
    (D : PEVolumeCutoffData X) :
    RenormalizedVolume D = finitePart D.volumeExpansion := by
  rfl

@[simp]
theorem VolumeAnomaly_eq_logAnomaly
    {X : PESpace}
    (D : PEVolumeCutoffData X) :
    VolumeAnomaly D = logAnomaly D.volumeExpansion := by
  rfl

end PE
end Ambient
end ConformalStructure
