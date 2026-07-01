import ConformalCovariantOperators.Ambient.PE.Basic
import ConformalCovariantOperators.Ambient.PE.Renormalization.FinitePart

open Classical

noncomputable section

universe u v w

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Generic cutoff functionals

The object type is unconstrained.  It may later be instantiated by a PE bulk,
a curvature invariant on a PE bulk, or an asymptotic submanifold.
-/

/-- A cutoff-dependent functional together with its Laurent--log expansion. -/
structure CutoffFunctional
    (Obj : Type u)
    (R : Type v)
    [Zero R] where
  cutoffValue : Obj -> PosReal -> R
  expansion : Obj -> LaurentLogExpansion R

namespace CutoffFunctional

variable
    {Obj : Type u}
    {R : Type v}
    [Zero R]

/-- The finite-part value of a cutoff functional. -/
def renormalizedValue
    (CF : CutoffFunctional Obj R)
    (obj : Obj) :
    R :=
  finitePart (CF.expansion obj)

/-- The logarithmic anomaly of a cutoff functional. -/
def anomalyValue
    (CF : CutoffFunctional Obj R)
    (obj : Obj) :
    R :=
  logAnomaly (CF.expansion obj)

@[simp]
theorem renormalizedValue_eq_coeff_zero
    (CF : CutoffFunctional Obj R)
    (obj : Obj) :
    CF.renormalizedValue obj = (CF.expansion obj).coeff 0 := by
  rfl

@[simp]
theorem anomalyValue_eq_logCoeff
    (CF : CutoffFunctional Obj R)
    (obj : Obj) :
    CF.anomalyValue obj = (CF.expansion obj).logCoeff := by
  rfl

end CutoffFunctional

/-- Top-level finite-part accessor for a cutoff functional. -/
def renormalizedValue
    {Obj : Type u}
    {R : Type v}
    [Zero R]
    (CF : CutoffFunctional Obj R)
    (obj : Obj) :
    R :=
  CF.renormalizedValue obj

/-- Top-level logarithmic-anomaly accessor for a cutoff functional. -/
def anomalyValue
    {Obj : Type u}
    {R : Type v}
    [Zero R]
    (CF : CutoffFunctional Obj R)
    (obj : Obj) :
    R :=
  CF.anomalyValue obj

/--
A packaged class of geometric objects carrying one common cutoff functional.

This is the extension point shared by volume, curvature integrals, and future
renormalized-area constructions.
-/
structure RenormalizableGeometricObject
    (R : Type v)
    [Zero R] where
  objectType : Type u
  cutoffFunctional : CutoffFunctional objectType R

end PE
end Ambient
end ConformalStructure
