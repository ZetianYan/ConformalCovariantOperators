import Mathlib
import ExtrinsicGJMSOperators.Geometry.Juhlformula.Juhlcombinatorics.LowOrderCheck
import ExtrinsicGJMSOperators.Geometry.Juhlformula.Juhloperators.Composition
import ExtrinsicGJMSOperators.Geometry.Juhlformula.Juhloperators.Coefficients

open Classical
open scoped BigOperators

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace Juhl

/-- Normalized equality of formal expressions. -/
def FormalEq (A B : FormalExpr) : Prop :=
  A.normalize = B.normalize

namespace FormalEq

theorem refl (A : FormalExpr) :
    FormalEq A A := by
  unfold FormalEq
  rfl

theorem trans {A B C : FormalExpr}
    (hAB : FormalEq A B)
    (hBC : FormalEq B C) :
    FormalEq A C := by
  unfold FormalEq at *
  exact hAB.trans hBC

theorem symm {A B : FormalExpr}
    (hAB : FormalEq A B) :
    FormalEq B A := by
  unfold FormalEq at *
  exact hAB.symm

end FormalEq

/-- Formal expression representing the composition `P_{2I} f`.

This is a syntax-level placeholder for the composition side. It is deliberately
not identified with the formal Laplacian-variation operators from the
obstruction recursion.
-/
def formalGJMSCompositionExpr
    {N : ℕ}
    (I : Composition N) : FormalExpr :=
  I.parts.foldr
    (fun j acc => FormalExpr.opD j acc)
    FormalExpr.f

/-- One term in a formal Juhl expansion. -/
structure FormalJuhlTerm where
  coeff : ℚ
  expr : FormalExpr
deriving Repr, DecidableEq

namespace FormalJuhlTerm

/-- Convert a formal Juhl term into syntax. -/
def toExpr (T : FormalJuhlTerm) : FormalExpr :=
  FormalExpr.qsmul T.coeff T.expr

end FormalJuhlTerm

/-- A finite formal Juhl right-hand side. -/
structure FormalJuhlRHS where
  terms : List FormalJuhlTerm
deriving Repr, DecidableEq

namespace FormalJuhlRHS

/-- Convert a finite formal Juhl RHS into syntax. -/
def toExpr (R : FormalJuhlRHS) : FormalExpr :=
  listSum (R.terms.map FormalJuhlTerm.toExpr)

end FormalJuhlRHS

/-- The formal Juhl formula at order `N`. -/
structure FormalJuhlStatement (N : ℕ) where
  rhs : FormalJuhlRHS
  formula : FormalEq (formalP N) rhs.toExpr

/-- The order-one formal Juhl statement, using the checked raw `P_2`. -/
def formalJuhlStatement_one : FormalJuhlStatement 1 where
  rhs := {
    terms := [
      { coeff := 1, expr := expectedP2 }
    ]
  }
  formula := by
    unfold FormalEq FormalJuhlRHS.toExpr FormalJuhlTerm.toExpr
    native_decide

/-- The order-two formal Juhl statement, using the checked raw `P_4`. -/
def formalJuhlStatement_two_raw : FormalJuhlStatement 2 where
  rhs := {
    terms := [
      { coeff := 1, expr := expectedP4Raw }
    ]
  }
  formula := by
    unfold FormalEq FormalJuhlRHS.toExpr FormalJuhlTerm.toExpr
    native_decide

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
