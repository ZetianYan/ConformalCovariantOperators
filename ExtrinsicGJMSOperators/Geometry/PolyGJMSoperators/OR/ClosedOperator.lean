import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OR.DefectCancellation
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OR.Coefficients.ClosedFormula

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
variable (CalConf : Calculus Conf)

/-!
# Closed regular OR operator data

This file connects the regular closed coefficient formula to the operator-data
layer. Tangentiality is still obtained from a recurrence/cancellation proof.
-/

namespace OROperatorData

/-- OR operator data using the regular closed coefficients. -/
def regular
    (N : ℕ)
    (n w₁ w₂ : ℚ) :
    OROperatorData where
  N := N
  w₁ := w₁
  w₂ := w₂
  n := n
  coeffSystem := ORCoefficientSystem.regular N n w₁ w₂

@[simp]
theorem regular_coeffSystem_coeff
    (N : ℕ)
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) :
    ((regular N n w₁ w₂).coeffSystem).coeff I =
      ORRegularCoeff n w₁ w₂ I := by
  rfl

/-- The regular closed OR operator. -/
def regularOperator
    (N : ℕ)
    (n w₁ w₂ : ℚ)
    (CalConf : Calculus Conf) :
    CalConf.BiOperator :=
  (regular N n w₁ w₂).toOperator CalConf

/--
Once the regular closed coefficients satisfy the chosen rational defect
cancellation equations, the regular closed OR operator is tangential.
-/
theorem regular_isBiTangential_of_rational_defect_cancellation
    {κ : Type _}
    [DecidableEq κ]
    (N : ℕ)
    (n w₁ w₂ : ℚ)
    {K : Finset κ}
    (E : (regular N n w₁ w₂).ORDefectExpansion CalConf K)
    (defectCoeffQ : ORIndex N → Fin 2 → κ → ℚ)
    (hE :
      ∀ (I : ORIndex N) (slot : Fin 2) (k : κ),
        E.defectCoeffR I slot k = (defectCoeffQ I slot k : ℝ))
    (hQ :
      (regular N n w₁ w₂).SatisfiesRationalDefectCancellation
        K defectCoeffQ) :
    CalConf.IsBiTangentialAtWeights
      ((regular N n w₁ w₂).toOperator CalConf)
      (w₁ : ℝ)
      (w₂ : ℝ) :=
  (regular N n w₁ w₂).isBiTangential_of_rational_defect_cancellation
    (CalConf := CalConf)
    E defectCoeffQ hE hQ

end OROperatorData

end Calculus
end Operators
end Ambient
end ConformalStructure
