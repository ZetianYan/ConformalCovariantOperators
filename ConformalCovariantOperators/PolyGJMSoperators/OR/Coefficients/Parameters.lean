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
# Parameters for the regular Ovsienko--Redou coefficient formula

These definitions translate the Gamma ratios in Theorem 1.1 into Pochhammer
parameters over `ℚ`.
-/

/-- The half-dimension shift `(n - 2N) / 2`. -/
def ORHalfShift (N : ℕ) (n : ℚ) : ℚ :=
  (n - 2 * (N : ℚ)) / 2

/-- Parameter for the numerator Gamma ratio depending on `s + t`. -/
def ORAlpha (N : ℕ) (n w₁ w₂ : ℚ) : ℚ :=
  -w₁ - w₂ - ORHalfShift N n

/-- Parameter for the first-input Gamma ratio. -/
def ORBeta (N : ℕ) (n w₁ : ℚ) : ℚ :=
  w₁ + ORHalfShift N n

/-- Parameter for the second-input Gamma ratio. -/
def ORGamma (N : ℕ) (n w₂ : ℚ) : ℚ :=
  w₂ + ORHalfShift N n

theorem ORAlpha_add_b_add_c
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) :
    ORAlpha N n w₁ w₂ + (I.b + I.c : ℕ) =
      -(2 * w₁ + 2 * w₂ + n - 2 * (N : ℚ) - 2 * I.b - 2 * I.c) / 2 := by
  unfold ORAlpha ORHalfShift
  norm_num [Nat.cast_add]
  ring_nf

end Calculus
end Operators
end Ambient
end ConformalStructure
