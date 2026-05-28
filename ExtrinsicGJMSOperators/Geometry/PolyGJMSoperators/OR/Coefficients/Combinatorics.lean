import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OR.Index

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
# Rational combinatorial coefficients

The OR coefficient layer is kept over `ℚ`; coefficients are cast to `ℝ` only
when building an ambient operator.
-/

/-- Factorial as a rational number. -/
def factorialQ (m : ℕ) : ℚ :=
  (Nat.factorial m : ℚ)

/-- Binomial coefficient as a rational number. -/
def binomQ (m j : ℕ) : ℚ :=
  (Nat.choose m j : ℚ)

/-- The trinomial/multinomial coefficient `N! / (a! b! c!)`. -/
def multinomialQ3 (N a b c : ℕ) : ℚ :=
  factorialQ N / (factorialQ a * factorialQ b * factorialQ c)

/-- Rising factorial / Pochhammer symbol `(x)_m`. -/
def pochhammerQ (x : ℚ) (m : ℕ) : ℚ :=
  (Finset.range m).prod fun j => x + (j : ℚ)

/-- Falling factorial `x(x-1)...(x-m+1)`. -/
def fallingFactorialQ (x : ℚ) (m : ℕ) : ℚ :=
  (Finset.range m).prod fun j => x - (j : ℚ)

@[simp]
theorem factorialQ_zero :
    factorialQ 0 = 1 := by
  simp [factorialQ]

theorem factorialQ_succ (m : ℕ) :
    factorialQ (m + 1) = ((m + 1 : ℕ) : ℚ) * factorialQ m := by
  simp [factorialQ, Nat.factorial_succ, mul_comm]

@[simp]
theorem binomQ_zero_right (m : ℕ) :
    binomQ m 0 = 1 := by
  simp [binomQ]

@[simp]
theorem binomQ_self (m : ℕ) :
    binomQ m m = 1 := by
  simp [binomQ]

@[simp]
theorem pochhammerQ_zero (x : ℚ) :
    pochhammerQ x 0 = 1 := by
  simp [pochhammerQ]

theorem pochhammerQ_succ (x : ℚ) (m : ℕ) :
    pochhammerQ x (m + 1) =
      pochhammerQ x m * (x + (m : ℚ)) := by
  simp [pochhammerQ, Finset.prod_range_succ]

@[simp]
theorem fallingFactorialQ_zero (x : ℚ) :
    fallingFactorialQ x 0 = 1 := by
  simp [fallingFactorialQ]

theorem fallingFactorialQ_succ (x : ℚ) (m : ℕ) :
    fallingFactorialQ x (m + 1) =
      fallingFactorialQ x m * (x - (m : ℚ)) := by
  simp [fallingFactorialQ, Finset.prod_range_succ]

theorem pochhammerQ_eq_pred_mul
    (x : ℚ)
    {m : ℕ}
    (hm : 0 < m) :
    pochhammerQ x m =
      pochhammerQ x (m - 1) * (x + ((m - 1 : ℕ) : ℚ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp [pochhammerQ_succ]

theorem fallingFactorialQ_eq_pred_mul
    (x : ℚ)
    {m : ℕ}
    (hm : 0 < m) :
    fallingFactorialQ x m =
      fallingFactorialQ x (m - 1) * (x - ((m - 1 : ℕ) : ℚ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp [fallingFactorialQ_succ]

end Calculus
end Operators
end Ambient
end ConformalStructure
