import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.OR.Coefficients.Combinatorics

open Classical
open scoped BigOperators

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus

variable {M : Type u}
variable {Conf : ConformalStructure.{u, v} M}

/-!
# OR coefficient systems and recurrence predicates

The geometric tangentiality proof only needs the coefficient recurrence in the
form of defect cancellation. The closed formula will later be proved to satisfy
this recurrence.
-/

/-- A rational coefficient system on the OR support of total degree `N`. -/
structure ORCoefficientSystem (N : ℕ) where
  coeff : ORIndex N → ℚ

namespace ORCoefficientSystem

/-- Coefficients cast to real numbers for ambient operators. -/
def coeffR {N : ℕ} (C : ORCoefficientSystem N) (I : ORIndex N) : ℝ :=
  (C.coeff I : ℝ)

@[simp]
theorem coeffR_apply {N : ℕ} (C : ORCoefficientSystem N) (I : ORIndex N) :
    C.coeffR I = (C.coeff I : ℝ) := by
  rfl

end ORCoefficientSystem

/--
Rational defect cancellation for an OR coefficient system.

`defectCoeffQ I slot k` is the rational coefficient of the obstruction `k`
created by the word indexed by `I` in the input slot `slot`.
-/
def SatisfiesDefectCancellationQ
    {N : ℕ}
    {κ : Type _}
    [DecidableEq κ]
    (K : Finset κ)
    (C : ORCoefficientSystem N)
    (defectCoeffQ : ORIndex N → Fin 2 → κ → ℚ) : Prop :=
  ∀ (slot : Fin 2) (k : κ), k ∈ K →
    ∑ I ∈ ORIndex.support N, C.coeff I * defectCoeffQ I slot k = 0

/--
The OR recurrence, recorded in the cancellation form used by the operator
proof. The parameters `w₁`, `w₂`, and `n` are kept here so the later
paper-specific recurrence can specialize this predicate without changing the
downstream API.
-/
def SatisfiesORRecurrence
    {N : ℕ}
    {κ : Type _}
    [DecidableEq κ]
    (_w₁ _w₂ _n : ℚ)
    (K : Finset κ)
    (C : ORCoefficientSystem N)
    (defectCoeffQ : ORIndex N → Fin 2 → κ → ℚ) : Prop :=
  SatisfiesDefectCancellationQ K C defectCoeffQ

theorem satisfiesORRecurrence_iff_defectCancellationQ
    {N : ℕ}
    {κ : Type _}
    [DecidableEq κ]
    (w₁ w₂ n : ℚ)
    (K : Finset κ)
    (C : ORCoefficientSystem N)
    (defectCoeffQ : ORIndex N → Fin 2 → κ → ℚ) :
    SatisfiesORRecurrence w₁ w₂ n K C defectCoeffQ ↔
      SatisfiesDefectCancellationQ K C defectCoeffQ := by
  rfl

end Calculus
end Operators
end Ambient
end ConformalStructure
