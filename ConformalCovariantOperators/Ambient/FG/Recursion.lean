import ConformalCovariantOperators.Ambient.FG.FormalJets

open Classical
open scoped BigOperators

noncomputable section

universe w

namespace ConformalStructure
namespace Ambient
namespace FG

variable {ι : Type w}

/-!
# Finite formal Ricci recursion scaffold

This file packages a finite recursive solution for the coefficients of
`g_rho`.  It does not claim existence or uniqueness yet; instead it provides the
stable data structure that later Ricci-equation calculations will fill.
-/

/-- A solved finite FG Ricci recursion for a formal metric jet. -/
structure FormalRicciRecursion
    (J : FormalMetricJet ι K) where
  /-- The recursively solved coefficient at each available order. -/
  solvedCoeff : (m : Fin (K + 1)) → Sym2Component ι
  /-- The recursion agrees with the jet coefficients. -/
  solvedCoeff_eq :
    ∀ (m : Fin (K + 1)) (i j : ι),
      solvedCoeff m i j = J.coeff m i j

namespace FormalRicciRecursion

variable {K : ℕ} {J : FormalMetricJet ι K}

/-- Access the solved coefficient at order `m <= K`. -/
def solvedAt
    (R : FormalRicciRecursion (ι := ι) J)
    (m : ℕ)
    (hm : m ≤ K) : Sym2Component ι :=
  R.solvedCoeff ⟨m, Nat.lt_succ_of_le hm⟩

@[simp]
theorem solvedAt_zero
    (R : FormalRicciRecursion (ι := ι) J) :
    R.solvedAt 0 (Nat.zero_le K) = J.baseMetric := by
  funext i j
  rw [solvedAt, R.solvedCoeff_eq]
  exact J.coeff_zero_eq_base i j

/-- The solved first coefficient is `2 * Schouten` under the first Ricci condition. -/
theorem solved_firstJet_eq_two_schouten
    (R : FormalRicciRecursion (ι := ι) J)
    (H : SatisfiesFGRicciToOrder J 1)
    (i j : ι) :
    R.solvedAt 1 H.order_le i j = 2 * J.schouten i j := by
  rw [solvedAt, R.solvedCoeff_eq]
  exact FG_first_jet J H i j

end FormalRicciRecursion

/--
Data asserting that the FG Ricci equations have been solved recursively to a
finite order.
-/
structure FGRicciSolvedToOrder
    (J : FormalMetricJet ι K)
    (order : ℕ) where
  conditions : SatisfiesFGRicciToOrder J order
  recursion : FormalRicciRecursion J

/-- The first solved coefficient of a finite FG solution is `2 * Schouten`. -/
theorem FGRicciSolvedToOrder.firstJet
    (S : FGRicciSolvedToOrder (ι := ι) J 1)
    (i j : ι) :
    S.recursion.solvedAt 1 S.conditions.order_le i j
      = 2 * J.schouten i j :=
  S.recursion.solved_firstJet_eq_two_schouten S.conditions i j

end FG
end Ambient
end ConformalStructure
