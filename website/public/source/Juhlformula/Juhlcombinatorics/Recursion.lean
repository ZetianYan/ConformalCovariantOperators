import Mathlib
import ConformalCovariantOperators.Juhlformula.Juhlcombinatorics.FormalJets

open Classical
open scoped BigOperators

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace Juhl

namespace FormalExpr

/-- Substitute all formal normal jets using a substitution function. -/
def substF (σ : ℕ → FormalExpr) : FormalExpr → FormalExpr
  | zero => zero
  | one => one
  | rat q => rat q
  | k => k
  | f => f
  | F m => σ m
  | tr j => tr j
  | add A B => substF σ A + substF σ B
  | neg A => - substF σ A
  | mul A B => substF σ A * substF σ B
  | opD j A => opD j (substF σ A)

end FormalExpr

/-- The scalar used to solve `L_s = 0` for `F_{s+1}`. -/
def solveStepCoeff (ell s : ℕ) : ℚ :=
  - (highestCoeff ell s)⁻¹

set_option linter.unusedVariables false in
/-- Recursive formal solution for normal jets. -/
def solvedJetAux (ell : ℕ) : ℕ → FormalExpr
  | 0 => FormalExpr.f
  | s + 1 =>
      let σ : ℕ → FormalExpr :=
        fun m =>
          if hm : m ≤ s then
            solvedJetAux ell m
          else
            FormalExpr.F m
      FormalExpr.qsmul (solveStepCoeff ell s)
        (FormalExpr.substF σ (Lrest ell s))
termination_by n => n
decreasing_by
  exact Nat.lt_succ_of_le hm

/-- The formal normal jet `F_m` solved from the obstruction recursion. -/
def solvedJet (ell m : ℕ) : FormalExpr :=
  solvedJetAux ell m

@[simp]
theorem solvedJet_zero (ell : ℕ) :
    solvedJet ell 0 = FormalExpr.f := by
  simp [solvedJet, solvedJetAux]

/-- Substitute every normal jet by the solved formal jet. -/
def solvedSubst (ell : ℕ) : ℕ → FormalExpr :=
  fun m => solvedJet ell m

/-- The formal obstruction coefficient `G_0`. -/
def obstructionCoeff (ell : ℕ) : FormalExpr :=
  match ell with
  | 0 => 0
  | ell' + 1 =>
      FormalExpr.substF (solvedSubst (ell' + 1))
        (Lcoeff (ell' + 1) ell')

@[simp]
theorem obstructionCoeff_one :
    obstructionCoeff 1 =
      FormalExpr.substF (solvedSubst 1) (Lcoeff 1 0) := by
  rfl

/-- The inverse normalization constant `a_ell^{-1}`. -/
def aEllInv (ell : ℕ) : ℚ :=
  match ell with
  | 0 => 0
  | ell' + 1 =>
      ((-1 : ℚ) ^ (ell' + 1))
        * (2 : ℚ) ^ (2 * ell')
        * (factQ ell') ^ 2

/-- The formal obstruction operator `P_{2 ell}` applied to the boundary value `f`. -/
def formalP (ell : ℕ) : FormalExpr :=
  FormalExpr.qsmul (aEllInv ell) (obstructionCoeff ell)

@[simp]
theorem aEllInv_one :
    aEllInv 1 = -1 := by
  norm_num [aEllInv, factQ]

@[simp]
theorem aEllInv_two :
    aEllInv 2 = 4 := by
  norm_num [aEllInv, factQ]

@[simp]
theorem aEllInv_three :
    aEllInv 3 = -64 := by
  norm_num [aEllInv, factQ]

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
