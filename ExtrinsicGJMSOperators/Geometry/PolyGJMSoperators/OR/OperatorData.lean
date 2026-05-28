import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OvsienkoRedou
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OR.Coefficients.Recurrence

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
# OR operator data from rational coefficients

This layer turns an OR coefficient system into a concrete rank-two ambient
operator. The sum is indexed directly by `ORIndex N`, avoiding any need to
recover triples from `LaplacianWord 2`.
-/

/-- Concrete OR operator data with rational coefficient parameters. -/
structure OROperatorData where
  N : ℕ
  w₁ : ℚ
  w₂ : ℚ
  n : ℚ
  coeffSystem : ORCoefficientSystem N

namespace OROperatorData

/-- Input weights cast to real numbers for the ambient calculus. -/
def inputWeights
    (D : OROperatorData)
    (CalConf : Calculus Conf) : Fin 2 → ℝ :=
  CalConf.biWeights (D.w₁ : ℝ) (D.w₂ : ℝ)

/-- Expected real output weight of an OR operator of total degree `N`. -/
def outputWeight (D : OROperatorData) : ℝ :=
  (D.w₁ : ℝ) + (D.w₂ : ℝ) - 2 * (D.N : ℝ)

/-- The rank-two ambient operator associated to the OR data. -/
def toOperator
    (D : OROperatorData)
    (CalConf : Calculus Conf) :
    CalConf.BiOperator :=
  CalConf.operatorSum
    (ORIndex.support D.N)
    (fun I => D.coeffSystem.coeffR I)
    (fun I => I.toWord.toOperator CalConf)

@[simp]
theorem toOperator_apply
    (D : OROperatorData)
    (F : CalConf.BiInput)
    (U : Conf.AmbientBundle) :
    D.toOperator CalConf F U =
      ∑ I ∈ ORIndex.support D.N,
        (D.coeffSystem.coeff I : ℝ) * I.toWord.toOperator CalConf F U := by
  rfl

theorem toWord_expectedOutputWeight
    (D : OROperatorData)
    (I : ORIndex D.N) :
    I.toWord.expectedOutputWeight CalConf (D.inputWeights CalConf) =
      D.outputWeight := by
  simp [LaplacianWord.expectedOutputWeight, inputWeights, outputWeight,
    CalConf.totalWeight_biWeights, I.toWord_totalPower]

/--
Weight mapping for the OR operator, assuming product homogeneity for words and
homogeneity of finite operator sums.
-/
theorem mapsWeights
    (D : OROperatorData)
    (H : CalConf.AlgebraicIdentities)
    (Hprod : CalConf.ProductHomogeneityIdentities)
    (Hsum :
      PolyLaplacianCombinationData.OperatorSumHomogeneityIdentities CalConf) :
    CalConf.MapsWeights
      (D.toOperator CalConf)
      (D.inputWeights CalConf)
      D.outputWeight := by
  unfold toOperator
  refine
    Hsum.operatorSum_mapsWeights
      (ORIndex.support D.N)
      (fun I => D.coeffSystem.coeffR I)
      (fun I : ORIndex D.N => I.toWord.toOperator CalConf)
      (D.inputWeights CalConf)
      D.outputWeight
      ?_
  intro I _hI F hF
  rw [← D.toWord_expectedOutputWeight (CalConf := CalConf) I]
  exact (I.toWord.mapsWeights H Hprod (D.inputWeights CalConf)) hF

/--
A word-indexed shadow of the OR data. This is useful for reusing the generic
Level 8 API, though `toOperator` above remains the preferred OR-indexed sum.
-/
def toOvsienkoRedouData
    (D : OROperatorData) :
    OvsienkoRedouData where
  N := D.N
  w₁ := (D.w₁ : ℝ)
  w₂ := (D.w₂ : ℝ)
  support := (ORIndex.support D.N).image (fun I => I.toWord)
  coeff := fun W =>
    ∑ I ∈ ORIndex.support D.N,
      if I.toWord = W then (D.coeffSystem.coeff I : ℝ) else 0
  support_totalPower := by
    intro W hW
    rcases Finset.mem_image.mp hW with ⟨I, _hI, rfl⟩
    exact I.toWord_totalPower

end OROperatorData

end Calculus
end Operators
end Ambient
end ConformalStructure
