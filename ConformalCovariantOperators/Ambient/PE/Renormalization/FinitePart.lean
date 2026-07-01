import ConformalCovariantOperators.Ambient.PE.Renormalization.LaurentLogExpansion

open Classical

noncomputable section

universe u

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Finite part and logarithmic anomaly
-/

/-- The constant Laurent coefficient. -/
def finitePart
    {R : Type u}
    [Zero R]
    (E : LaurentLogExpansion R) :
    R :=
  E.coeff 0

/-- The coefficient of `log(epsilon)`. -/
def logAnomaly
    {R : Type u}
    [Zero R]
    (E : LaurentLogExpansion R) :
    R :=
  E.logCoeff

/-- The assertion that an expansion contains no logarithmic anomaly. -/
def HasNoLogTerm
    {R : Type u}
    [Zero R]
    (E : LaurentLogExpansion R) :
    Prop :=
  E.logCoeff = 0

@[simp]
theorem finitePart_eq_coeff_zero
    {R : Type u}
    [Zero R]
    (E : LaurentLogExpansion R) :
    finitePart E = E.coeff 0 := by
  rfl

@[simp]
theorem logAnomaly_eq_logCoeff
    {R : Type u}
    [Zero R]
    (E : LaurentLogExpansion R) :
    logAnomaly E = E.logCoeff := by
  rfl

end PE
end Ambient
end ConformalStructure
