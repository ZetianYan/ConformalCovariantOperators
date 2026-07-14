import Mathlib
import ConformalCovariantOperators.Juhlformula.Juhlcombinatorics.FormalStatement
import ConformalCovariantOperators.PolyGJMSoperators.OR
import ConformalCovariantOperators.PolyGJMSoperators.PolyLaplacianCombination
import ConformalCovariantOperators.PolyGJMSoperators.OvsienkoRedou

open Classical
open scoped BigOperators

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace Juhl

/-- A bridge between one Juhl composition term and one OR/poly-laplacian term.

This is intentionally abstract in the first version. Later versions can
replace `orExpr` by a concrete OR operator object and keep this as the formal
shadow.
-/
structure ORBridgeTerm where
  juhlCoeff : ℚ
  juhlExpr : FormalExpr
  orCoeff : ℚ
  orExpr : FormalExpr
  coeff_eq : juhlCoeff = orCoeff
  expr_eq : FormalEq juhlExpr orExpr

/-- A finite bridge between a formal Juhl RHS and an OR RHS. -/
structure ORBridge where
  juhlRHS : FormalJuhlRHS
  orRHS : FormalJuhlRHS
  bridge_eq : FormalEq juhlRHS.toExpr orRHS.toExpr

namespace ORBridge

/-- The identity bridge from a RHS to itself. -/
def refl (R : FormalJuhlRHS) : ORBridge where
  juhlRHS := R
  orRHS := R
  bridge_eq := FormalEq.refl R.toExpr

end ORBridge

/-- Placeholder for later conversion from actual OR data to a formal RHS. -/
structure ORFormalizationData where
  order : ℕ
  rhs : FormalJuhlRHS

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
