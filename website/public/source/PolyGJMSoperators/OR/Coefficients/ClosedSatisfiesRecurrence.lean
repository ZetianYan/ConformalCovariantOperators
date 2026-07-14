import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.OR.Coefficients.RatioLemmas

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
# Closed regular coefficients and recurrence

This file is the intended home for the proof that the regular closed OR
coefficients satisfy the defect-cancellation recurrence. At this stage it
records the clean bridge from a rational cancellation proof to the closed-form
recurrence predicate.
-/

/--
The regular closed formula satisfies the OR recurrence as soon as the chosen
rational defect coefficients cancel against the regular closed coefficient
system.
-/
theorem ORRegularClosedFormula_satisfiesRecurrence_of_defectCancellationQ
    {N : ℕ}
    {κ : Type _}
    [DecidableEq κ]
    (n w₁ w₂ : ℚ)
    (K : Finset κ)
    (defectCoeffQ : ORIndex N → Fin 2 → κ → ℚ)
    (hcancel :
      SatisfiesDefectCancellationQ
        K
        (ORCoefficientSystem.regular N n w₁ w₂)
        defectCoeffQ) :
    ORRegularClosedFormula.SatisfiesRecurrence
      n w₁ w₂ K defectCoeffQ := by
  exact hcancel

/--
The regular closed formula supplies Gamma-ratio coefficients satisfying the two
local recurrence equations of Lemma 3.1.
-/
theorem ORRegularClosedFormula_satisfiesLemma31LocalRecurrences
    {N : ℕ}
    (n w₁ w₂ : ℚ) :
    (∀ I : ORIndex N, ORRegularAFirstRecurrence n w₁ w₂ I)
      ∧
    (∀ I : ORIndex N, ORRegularASecondRecurrence n w₁ w₂ I) :=
  ORRegularA_satisfiesLemma31Recurrences n w₁ w₂

end Calculus
end Operators
end Ambient
end ConformalStructure
