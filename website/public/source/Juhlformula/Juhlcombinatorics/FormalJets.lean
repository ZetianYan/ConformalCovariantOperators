import Mathlib
import ConformalCovariantOperators.Juhlformula.Juhloperators.Coefficients

open Classical
open scoped BigOperators

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace Juhl

/-- Formal expressions used in the Juhl obstruction recursion. -/
inductive FormalExpr where
  | zero : FormalExpr
  | one : FormalExpr
  | rat : ℚ → FormalExpr
  | k : FormalExpr
  | f : FormalExpr
  | F : ℕ → FormalExpr
  | tr : ℕ → FormalExpr
  | add : FormalExpr → FormalExpr → FormalExpr
  | neg : FormalExpr → FormalExpr
  | mul : FormalExpr → FormalExpr → FormalExpr
  | opD : ℕ → FormalExpr → FormalExpr
deriving Repr, DecidableEq

namespace FormalExpr

instance : Zero FormalExpr := ⟨FormalExpr.zero⟩
instance : One FormalExpr := ⟨FormalExpr.one⟩
instance : Neg FormalExpr := ⟨FormalExpr.neg⟩
instance : Add FormalExpr := ⟨FormalExpr.add⟩
instance : Sub FormalExpr := ⟨fun A B => A + -B⟩
instance : Mul FormalExpr := ⟨FormalExpr.mul⟩

/-- Rational scalar multiplication as syntax. -/
def qsmul (q : ℚ) (E : FormalExpr) : FormalExpr :=
  FormalExpr.mul (FormalExpr.rat q) E

end FormalExpr

/-- Rational factorial. -/
def factQ (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ)

/-- `1 / n!` as a rational number. -/
def invFactQ (n : ℕ) : ℚ :=
  (factQ n)⁻¹

/-- The Taylor denominator `1 / (a! b!)`. -/
def invFact2Q (a b : ℕ) : ℚ :=
  (factQ a * factQ b)⁻¹

/-- Sum a list of formal expressions at the syntax level. -/
def listSum : List FormalExpr → FormalExpr
  | [] => 0
  | x :: xs => x + listSum xs

/-- Sum over `0, ..., m` at the syntax level. -/
def rangeSum (m : ℕ) (A : ℕ → FormalExpr) : FormalExpr :=
  listSum ((List.range (m + 1)).map A)

/-- Coefficient of the highest jet `F_{m+1}` in `L_m`. -/
def highestCoeff (ell m : ℕ) : ℚ :=
  4 * ((m + 1 : ℚ) - (ell : ℚ)) * invFactQ m

/-- The trace-times-radial-derivative part of `L_m`. -/
def traceDerivativePart : ℕ → FormalExpr
  | 0 => 0
  | m' + 1 =>
      rangeSum m' fun j =>
        FormalExpr.qsmul (2 * invFact2Q j (m' - j))
          ((FormalExpr.tr j) * (FormalExpr.F (m' + 1 - j)))

/-- The formal Laplacian-variation part of `L_m`. -/
def deltaPart (m : ℕ) : FormalExpr :=
  rangeSum m fun j =>
    FormalExpr.qsmul (invFact2Q j (m - j))
      (FormalExpr.opD j (FormalExpr.F (m - j)))

/-- The formal scalar factor `k / 2 - ell`. -/
def kOverTwoMinusEll (ell : ℕ) : FormalExpr :=
  FormalExpr.qsmul ((1 / 2 : ℚ)) FormalExpr.k
    + FormalExpr.qsmul (-(ell : ℚ)) FormalExpr.one

/-- The zeroth-order trace part of `L_m`. -/
def traceZerothPart (ell m : ℕ) : FormalExpr :=
  (kOverTwoMinusEll ell) *
    (rangeSum m fun j =>
      FormalExpr.qsmul (invFact2Q j (m - j))
        ((FormalExpr.tr j) * (FormalExpr.F (m - j))))

/-- The part of `L_m` not containing the distinguished highest jet `F_{m+1}`. -/
def Lrest (ell m : ℕ) : FormalExpr :=
  traceDerivativePart m
    + deltaPart m
    + traceZerothPart ell m

/-- The full coefficient equation `L_m`. -/
def Lcoeff (ell m : ℕ) : FormalExpr :=
  FormalExpr.qsmul (highestCoeff ell m) (FormalExpr.F (m + 1))
    + Lrest ell m

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
