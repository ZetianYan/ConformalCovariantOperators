import Mathlib
import ConformalCovariantOperators.Juhlformula.Juhlcombinatorics.Recursion

open Classical
open scoped BigOperators

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace Juhl

namespace FormalExpr

/-- Normalize a rational literal as syntax. -/
def normalizeRat (q : ℚ) : FormalExpr :=
  if q = 0 then
    zero
  else if q = 1 then
    one
  else
    rat q

/-- A small syntax normalizer for low-order raw checks.

This only removes syntactic zeros and ones and evaluates rational products.
It does not commute, associate, or distribute addition and multiplication.
-/
def normalize : FormalExpr → FormalExpr
  | zero => zero
  | one => one
  | rat q => normalizeRat q
  | k => k
  | f => f
  | F m => F m
  | tr j => tr j
  | add A B =>
      match normalize A, normalize B with
      | zero, B' => B'
      | A', zero => A'
      | A', B' => add A' B'
  | neg A =>
      match normalize A with
      | zero => zero
      | A' => neg A'
  | mul A B =>
      match normalize A, normalize B with
      | zero, _ => zero
      | _, zero => zero
      | one, B' => B'
      | A', one => A'
      | rat q, rat r => normalizeRat (q * r)
      | rat q, _ => if q = 0 then zero else mul (rat q) (normalize B)
      | _, rat q => if q = 0 then zero else mul (normalize A) (rat q)
      | A', B' => mul A' B'
  | opD j A =>
      opD j (normalize A)

end FormalExpr

/-- Expected raw first-order solved jet for the `ell = 2` recursion. -/
def expectedF1ForP4 : FormalExpr :=
  FormalExpr.qsmul ((1 / 4 : ℚ))
    (FormalExpr.opD 0 FormalExpr.f
      + kOverTwoMinusEll 2 * ((FormalExpr.tr 0) * FormalExpr.f))

/-- Raw formal `P_2`, before distributing the scalar `-1`. -/
def expectedP2 : FormalExpr :=
  FormalExpr.qsmul (-1)
    (FormalExpr.opD 0 FormalExpr.f
      + kOverTwoMinusEll 1 * ((FormalExpr.tr 0) * FormalExpr.f))

/-- Expanded display form of the expected formal `P_2`. -/
def expectedP2Expanded : FormalExpr :=
  - FormalExpr.opD 0 FormalExpr.f
    - (FormalExpr.qsmul ((1 / 2 : ℚ)) FormalExpr.k)
        * (FormalExpr.tr 0) * FormalExpr.f
    + (FormalExpr.tr 0) * FormalExpr.f

/-- Raw formal `P_4`, keeping `D_0` unapplied to products. -/
def expectedP4Raw : FormalExpr :=
  FormalExpr.qsmul 4
    (FormalExpr.qsmul 2 ((FormalExpr.tr 0) * expectedF1ForP4)
      + (FormalExpr.opD 0 expectedF1ForP4
          + FormalExpr.opD 1 FormalExpr.f)
      + kOverTwoMinusEll 2 *
          (((FormalExpr.tr 0) * expectedF1ForP4)
            + (FormalExpr.tr 1) * FormalExpr.f))

theorem formalP_one_eq_expectedP2 :
    (formalP 1).normalize = expectedP2.normalize := by
  native_decide

theorem formalP_two_eq_expectedP4Raw :
    (formalP 2).normalize = expectedP4Raw.normalize := by
  native_decide

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
