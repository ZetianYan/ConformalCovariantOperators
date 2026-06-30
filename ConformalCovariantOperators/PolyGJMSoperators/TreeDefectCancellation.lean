import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.TreeRecurrence
import ConformalCovariantOperators.PolyGJMSoperators.LinearCombination

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
variable (CalConf : Calculus Conf)

/-!
# Tree-word defect cancellation interface

The hard analytic theorem still to prove is the commutator defect formula for
nested left-comb words.  This file packages the exact interface needed by the
rest of the project:

* finite sums of left-comb tree words;
* the rank-general recurrence on coefficients;
* a principle saying that this recurrence implies weighted tangentiality.

No self-adjointness assumptions are included here.
-/

namespace LeftComb

/-- A finite linear combination of left-comb tree words of total degree `k`. -/
structure OperatorData (r k : ℕ) where
  support : Finset (CombIndex r k)
  coeff : CombCoeffSpace r k

namespace OperatorData

/-- The rank-`r` ambient operator associated to a finite tree-word sum. -/
def toOperator {r k : ℕ}
    (D : OperatorData r k)
    (CalConf : Calculus Conf) :
    CalConf.MultiOperator r :=
  CalConf.operatorSum D.support D.coeff
    (fun I => I.toOperator CalConf)

@[simp]
theorem toOperator_apply {r k : ℕ}
    (D : OperatorData r k)
    (F : CalConf.MultiInput r)
    (U : Conf.AmbientBundle) :
    D.toOperator CalConf F U =
      ∑ I ∈ D.support,
        D.coeff I * I.toOperator CalConf F U := by
  rfl

end OperatorData

/-- The still-to-be-proved commutator/tangentiality principle for left-comb
tree words.

Mathematically this is the statement that the path-wise recurrence cancels all
slot-wise `Q`-commutator defects, hence the ambient operator descends to the
boundary at the specified input weights.
-/
structure RecurrenceImpliesTangentiality
    (CalConf : Calculus Conf)
    (r k : ℕ)
    (w : Fin r → ℝ) : Prop where
  tangential_of_recurrence :
    ∀ D : OperatorData r k,
      RankRecurrence CalConf.n w D.coeff →
        CalConf.IsTangentialAtWeights (D.toOperator CalConf) w

/-- Apply a supplied defect-cancellation principle to obtain tangentiality. -/
theorem recurrence_implies_tangential {r k : ℕ}
    {w : Fin r → ℝ}
    (H : RecurrenceImpliesTangentiality CalConf r k w)
    (D : OperatorData r k)
    (hrec : RankRecurrence CalConf.n w D.coeff) :
    CalConf.IsTangentialAtWeights (D.toOperator CalConf) w :=
  H.tangential_of_recurrence D hrec

/-- Data certifying that a finite tree-word operator is tangential by
recurrence.
-/
structure TangentialOperatorData
    (r k : ℕ)
    (w : Fin r → ℝ) where
  operatorData : OperatorData r k
  recurrence : RankRecurrence CalConf.n w operatorData.coeff
  principle : RecurrenceImpliesTangentiality CalConf r k w

namespace TangentialOperatorData

/-- The ambient operator carried by a recurrence-certified data set. -/
def toOperator {r k : ℕ} {w : Fin r → ℝ}
    (D : TangentialOperatorData CalConf r k w) :
    CalConf.MultiOperator r :=
  D.operatorData.toOperator CalConf

/-- The certified tangentiality theorem. -/
theorem tangential {r k : ℕ} {w : Fin r → ℝ}
    (D : TangentialOperatorData CalConf r k w) :
    CalConf.IsTangentialAtWeights D.toOperator w := by
  exact recurrence_implies_tangential CalConf D.principle
    D.operatorData D.recurrence

end TangentialOperatorData

end LeftComb

end Calculus
end Operators
end Ambient
end ConformalStructure
