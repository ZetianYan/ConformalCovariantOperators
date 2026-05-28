import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OR.Coefficients.Parameters
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OR.Coefficients.Recurrence

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
# Closed coefficient formula interface

The exact paper formula should instantiate `ORClosedCoefficientFormula`. Keeping
the formula in this container prevents the closed-form combinatorics from
blocking the recurrence-to-tangentiality theorem.
-/

/-- A closed formula for OR rational coefficients. -/
structure ORClosedCoefficientFormula where
  coeff :
    (N : ℕ) → (n w₁ w₂ : ℚ) → ORIndex N → ℚ

namespace ORClosedCoefficientFormula

/-- The coefficient system associated to a closed formula. -/
def toCoefficientSystem
    (Φ : ORClosedCoefficientFormula)
    (N : ℕ)
    (n w₁ w₂ : ℚ) :
    ORCoefficientSystem N where
  coeff := Φ.coeff N n w₁ w₂

@[simp]
theorem toCoefficientSystem_coeff
    (Φ : ORClosedCoefficientFormula)
    (N : ℕ)
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) :
    (Φ.toCoefficientSystem N n w₁ w₂).coeff I =
      Φ.coeff N n w₁ w₂ I := by
  rfl

/-- A closed formula satisfies the OR recurrence for a chosen defect basis. -/
def SatisfiesRecurrence
    {N : ℕ}
    {κ : Type _}
    [DecidableEq κ]
    (Φ : ORClosedCoefficientFormula)
    (n w₁ w₂ : ℚ)
    (K : Finset κ)
    (defectCoeffQ : ORIndex N → Fin 2 → κ → ℚ) : Prop :=
  SatisfiesORRecurrence
    w₁ w₂ n K
    (Φ.toCoefficientSystem N n w₁ w₂)
    defectCoeffQ

end ORClosedCoefficientFormula

/-! ## Regular Ovsienko--Redou closed coefficient -/

/-- The multinomial factor in the regular OR formula. -/
def ORRegularMultinomialFactor {N : ℕ} (I : ORIndex N) : ℚ :=
  multinomialQ3 N I.a I.b I.c

/--
The regular Gamma-ratio part `a_{s,t}` of the OR formula, expressed via
Pochhammer symbols. Here `I.b = s` and `I.c = t`.
-/
def ORRegularA
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) : ℚ :=
  pochhammerQ (ORAlpha N n w₁ w₂) (I.b + I.c)
    * pochhammerQ (ORBeta N n w₁) (N - I.b)
    * pochhammerQ (ORGamma N n w₂) (N - I.c)

/-- The regular OR coefficient attached to an index `(a,b,c)`. -/
def ORRegularCoeff
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) : ℚ :=
  ORRegularMultinomialFactor I * ORRegularA n w₁ w₂ I

/-- The regular closed formula from Theorem 1.1, in rational/Pochhammer form. -/
def ORRegularClosedFormula : ORClosedCoefficientFormula where
  coeff := fun _ n w₁ w₂ I => ORRegularCoeff n w₁ w₂ I

/-- The regular OR coefficient system. -/
def ORCoefficientSystem.regular
    (N : ℕ)
    (n w₁ w₂ : ℚ) :
    ORCoefficientSystem N :=
  ORRegularClosedFormula.toCoefficientSystem N n w₁ w₂

@[simp]
theorem ORCoefficientSystem.regular_coeff
    (N : ℕ)
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) :
    (ORCoefficientSystem.regular N n w₁ w₂).coeff I =
      ORRegularCoeff n w₁ w₂ I := by
  rfl

end Calculus
end Operators
end Ambient
end ConformalStructure
