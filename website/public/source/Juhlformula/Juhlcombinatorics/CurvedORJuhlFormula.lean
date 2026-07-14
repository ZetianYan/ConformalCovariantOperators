import Mathlib
import ConformalCovariantOperators.Juhlformula.Juhlcombinatorics.ORBridge
import ConformalCovariantOperators.Juhlformula.Juhloperators.GJMSComposition

open Classical
open scoped BigOperators

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace Juhl

/-- Formal curved OR Juhl-type formula at order `N`.

This states that the obstruction-side operator `formalP N` agrees with an
OR-side RHS, through a formal Juhl RHS and a bridge.
-/
structure CurvedORJuhlTypeFormula (N : ℕ) where
  juhlStatement : FormalJuhlStatement N
  bridge : ORBridge
  bridge_matches :
    bridge.juhlRHS = juhlStatement.rhs

namespace CurvedORJuhlTypeFormula

/-- The OR side of a formal curved OR Juhl-type formula. -/
def orSide
    {N : ℕ}
    (F : CurvedORJuhlTypeFormula N) : FormalExpr :=
  F.bridge.orRHS.toExpr

/-- The formal curved OR Juhl-type identity. -/
theorem formula
    {N : ℕ}
    (F : CurvedORJuhlTypeFormula N) :
    FormalEq (formalP N) F.orSide := by
  apply FormalEq.trans F.juhlStatement.formula
  unfold orSide
  rw [← F.bridge_matches]
  exact F.bridge.bridge_eq

end CurvedORJuhlTypeFormula

/-- The order-one curved OR Juhl formula, with the identity bridge. -/
def curvedORJuhlFormula_one : CurvedORJuhlTypeFormula 1 where
  juhlStatement := formalJuhlStatement_one
  bridge := ORBridge.refl formalJuhlStatement_one.rhs
  bridge_matches := rfl

theorem curvedORJuhlFormula_one_identity :
    FormalEq (formalP 1) curvedORJuhlFormula_one.orSide :=
  CurvedORJuhlTypeFormula.formula curvedORJuhlFormula_one

/-- The order-two curved OR Juhl formula, with the raw `P_4` identity bridge. -/
def curvedORJuhlFormula_two_raw : CurvedORJuhlTypeFormula 2 where
  juhlStatement := formalJuhlStatement_two_raw
  bridge := ORBridge.refl formalJuhlStatement_two_raw.rhs
  bridge_matches := rfl

theorem curvedORJuhlFormula_two_raw_identity :
    FormalEq (formalP 2) curvedORJuhlFormula_two_raw.orSide :=
  CurvedORJuhlTypeFormula.formula curvedORJuhlFormula_two_raw

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
