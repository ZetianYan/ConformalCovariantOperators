import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.OR.OperatorData

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

namespace OROperatorData

/-!
# Defect cancellation for OR-indexed operators

This file closes the abstract OR layer: once the coefficient recurrence is
expressed as cancellation of all obstruction coefficients, the OR operator is
tangential.
-/

/-- OR-indexed defect expansion for a fixed operator datum. -/
structure ORDefectExpansion
    {κ : Type _}
    [DecidableEq κ]
    (D : OROperatorData)
    (CalConf : Calculus Conf)
    (K : Finset κ) where
  obstruction : Fin 2 → κ → CalConf.BiOperator
  defectCoeffR : ORIndex D.N → Fin 2 → κ → ℝ
  combination_defect :
    ∀ {F G : CalConf.BiInput},
      CalConf.IsMultiHomogeneous (D.inputWeights CalConf) F →
      CalConf.IsMultiHomogeneous (D.inputWeights CalConf) G →
      CalConf.SameBoundaryValueAtWeights (D.inputWeights CalConf) F G →
        CalConf.SameBoundaryValue
          (fun U => D.toOperator CalConf F U - D.toOperator CalConf G U)
          (fun U =>
            ∑ slot : Fin 2,
              ∑ k ∈ K,
                (∑ I ∈ ORIndex.support D.N,
                    (D.coeffSystem.coeff I : ℝ) * defectCoeffR I slot k)
                  * obstruction slot k F U)

/-- Real-valued OR defect cancellation. -/
def SatisfiesDefectCancellation
    {κ : Type _}
    [DecidableEq κ]
    (D : OROperatorData)
    (CalConf : Calculus Conf)
    {K : Finset κ}
    (E : D.ORDefectExpansion CalConf K) : Prop :=
  ∀ (slot : Fin 2) (k : κ), k ∈ K →
    ∑ I ∈ ORIndex.support D.N,
      (D.coeffSystem.coeff I : ℝ) * E.defectCoeffR I slot k = 0

/-- Rational-valued OR defect cancellation, before casting to `ℝ`. -/
def SatisfiesRationalDefectCancellation
    {κ : Type _}
    [DecidableEq κ]
    (D : OROperatorData)
    (K : Finset κ)
    (defectCoeffQ : ORIndex D.N → Fin 2 → κ → ℚ) : Prop :=
  SatisfiesDefectCancellationQ K D.coeffSystem defectCoeffQ

theorem satisfiesDefectCancellation_of_rational
    {κ : Type _}
    [DecidableEq κ]
    (D : OROperatorData)
    {K : Finset κ}
    (E : D.ORDefectExpansion CalConf K)
    (defectCoeffQ : ORIndex D.N → Fin 2 → κ → ℚ)
    (hE :
      ∀ (I : ORIndex D.N) (slot : Fin 2) (k : κ),
        E.defectCoeffR I slot k = (defectCoeffQ I slot k : ℝ))
    (hQ : D.SatisfiesRationalDefectCancellation K defectCoeffQ) :
    D.SatisfiesDefectCancellation CalConf E := by
  intro slot k hk
  simpa [SatisfiesRationalDefectCancellation, hE] using
    congrArg (fun q : ℚ => (q : ℝ)) (hQ slot k hk)

private theorem sameBoundaryValue_of_difference_sameBoundaryValue_zero
    {f g : Function Conf}
    (h :
      CalConf.SameBoundaryValue
        (fun U => f U - g U)
        (zero Conf)) :
    CalConf.SameBoundaryValue f g := by
  unfold SameBoundaryValue EqModQ VanishesModQ at h ⊢
  rcases h with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  funext U
  have haU := congrArg (fun F : Function Conf => F U) ha
  unfold zero at haU
  simpa using haU

/-- OR defect cancellation implies bidifferential tangentiality. -/
theorem isBiTangential_of_defect_cancellation
    {κ : Type _}
    [DecidableEq κ]
    (D : OROperatorData)
    {K : Finset κ}
    (E : D.ORDefectExpansion CalConf K)
    (hcancel : D.SatisfiesDefectCancellation CalConf E) :
    CalConf.IsBiTangentialAtWeights
      (D.toOperator CalConf)
      (D.w₁ : ℝ)
      (D.w₂ : ℝ) := by
  unfold IsBiTangentialAtWeights
  change
    CalConf.IsTangentialAtWeights
      (D.toOperator CalConf)
      (D.inputWeights CalConf)
  intro F G hF hG hFG
  have hdef := E.combination_defect hF hG hFG
  let defectSum : Function Conf :=
    fun U =>
      ∑ slot : Fin 2,
        ∑ k ∈ K,
          (∑ I ∈ ORIndex.support D.N,
              (D.coeffSystem.coeff I : ℝ) * E.defectCoeffR I slot k)
            * E.obstruction slot k F U
  have hdefectZero : defectSum = zero Conf := by
    funext U
    simp only [defectSum, zero]
    refine Finset.sum_eq_zero ?_
    intro slot _hslot
    refine Finset.sum_eq_zero ?_
    intro k hk
    simp [hcancel slot k hk]
  have hzero :
      CalConf.SameBoundaryValue defectSum (zero Conf) :=
    CalConf.SameBoundaryValue_of_eq hdefectZero
  have hdiffZero :
      CalConf.SameBoundaryValue
        (fun U => D.toOperator CalConf F U - D.toOperator CalConf G U)
        (zero Conf) := by
    exact CalConf.SameBoundaryValue_trans hdef hzero
  exact
    sameBoundaryValue_of_difference_sameBoundaryValue_zero
      (CalConf := CalConf)
      hdiffZero

/-- Rational recurrence/cancellation implies bidifferential tangentiality. -/
theorem isBiTangential_of_rational_defect_cancellation
    {κ : Type _}
    [DecidableEq κ]
    (D : OROperatorData)
    {K : Finset κ}
    (E : D.ORDefectExpansion CalConf K)
    (defectCoeffQ : ORIndex D.N → Fin 2 → κ → ℚ)
    (hE :
      ∀ (I : ORIndex D.N) (slot : Fin 2) (k : κ),
        E.defectCoeffR I slot k = (defectCoeffQ I slot k : ℝ))
    (hQ : D.SatisfiesRationalDefectCancellation K defectCoeffQ) :
    CalConf.IsBiTangentialAtWeights
      (D.toOperator CalConf)
      (D.w₁ : ℝ)
      (D.w₂ : ℝ) :=
  D.isBiTangential_of_defect_cancellation
    (CalConf := CalConf)
    E
    (D.satisfiesDefectCancellation_of_rational
      (CalConf := CalConf)
      E defectCoeffQ hE hQ)

/-- Package a proved OR operator as a weighted bidifferential operator. -/
def toWeightedBiTangentialOperator
    (D : OROperatorData)
    (hmaps :
      CalConf.MapsWeights
        (D.toOperator CalConf)
        (D.inputWeights CalConf)
        D.outputWeight)
    (htangential :
      CalConf.IsBiTangentialAtWeights
        (D.toOperator CalConf)
        (D.w₁ : ℝ)
        (D.w₂ : ℝ)) :
    CalConf.WeightedBiTangentialOperator where
  inputWeights := D.inputWeights CalConf
  outputWeight := D.outputWeight
  toOperator := D.toOperator CalConf
  mapsWeights := hmaps
  tangential := by
    intro F G hF hG hFG
    have ht :
        CalConf.IsTangentialAtWeights
          (D.toOperator CalConf)
          (CalConf.biWeights (D.w₁ : ℝ) (D.w₂ : ℝ)) := by
      exact htangential
    simpa [inputWeights] using ht hF hG hFG

end OROperatorData

end Calculus
end Operators
end Ambient
end ConformalStructure
