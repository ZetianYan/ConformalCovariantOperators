import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.PolyLaplacianCombination

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
# Ovsienko--Redou-style bidifferential data

This file specializes the rank-r Laplacian-combination framework to rank `2`.
The concrete closed-form coefficients and recurrence from the paper are left
as a later combinatorial layer; here we formalize the data, defect-cancellation
interface, and construction of weighted bidifferential tangential operators.
-/

/-- Data for a rank-two Ovsienko--Redou-style Laplacian-word combination. -/
structure OvsienkoRedouData where
  N : ℕ
  w₁ : ℝ
  w₂ : ℝ
  support : Finset (LaplacianWord 2)
  coeff : LaplacianWord 2 → ℝ
  support_totalPower :
    ∀ W ∈ support, W.totalPower = N

namespace OvsienkoRedouData

/-- Input weights as a rank-two multiweight. -/
def inputWeights
    (D : OvsienkoRedouData)
    (CalConf : Calculus Conf) : Fin 2 → ℝ :=
  CalConf.biWeights D.w₁ D.w₂

/-- The expected output weight. -/
def outputWeight
    (D : OvsienkoRedouData) : ℝ :=
  D.w₁ + D.w₂ - 2 * (D.N : ℝ)

/-- Forget the named bidifferential weights and view the data as rank-r data. -/
def toPolyData
    (D : OvsienkoRedouData)
    (CalConf : Calculus Conf) :
    PolyLaplacianCombinationData 2 where
  N := D.N
  inputWeights := D.inputWeights CalConf
  support := D.support
  coeff := D.coeff
  support_totalPower := D.support_totalPower

/-- The bidifferential operator represented by the data. -/
def toOperator
    (D : OvsienkoRedouData)
    (CalConf : Calculus Conf) :
    CalConf.BiOperator :=
  (D.toPolyData CalConf).toOperator CalConf

@[simp]
theorem toOperator_apply
    (D : OvsienkoRedouData)
    (F : CalConf.BiInput)
    (U : Conf.AmbientBundle) :
    D.toOperator CalConf F U =
      ∑ W ∈ D.support,
        D.coeff W * W.toOperator CalConf F U := by
  rfl

theorem poly_outputWeight_eq
    (D : OvsienkoRedouData) :
    (D.toPolyData CalConf).outputWeight CalConf =
      D.outputWeight := by
  unfold PolyLaplacianCombinationData.outputWeight outputWeight toPolyData inputWeights
  simpa [biOutputWeight] using
    (CalConf.biOutputWeight_eq D.w₁ D.w₂ D.N)

/-- Weight mapping under the abstract product and sum homogeneity assumptions. -/
theorem mapsWeights
    (D : OvsienkoRedouData)
    (H : CalConf.AlgebraicIdentities)
    (Hprod : CalConf.ProductHomogeneityIdentities)
    (Hsum :
      PolyLaplacianCombinationData.OperatorSumHomogeneityIdentities CalConf) :
    CalConf.MapsWeights
      (D.toOperator CalConf)
      (D.inputWeights CalConf)
      D.outputWeight := by
  have hmaps :
      CalConf.MapsWeights
        ((D.toPolyData CalConf).toOperator CalConf)
        (D.toPolyData CalConf).inputWeights
        ((D.toPolyData CalConf).outputWeight CalConf) :=
    (D.toPolyData CalConf).mapsWeights
      (CalConf := CalConf)
      H Hprod Hsum
  change
    CalConf.MapsWeights
      ((D.toPolyData CalConf).toOperator CalConf)
      (D.inputWeights CalConf)
      D.outputWeight
  intro F hF
  rw [← D.poly_outputWeight_eq (CalConf := CalConf)]
  exact hmaps hF

/-- Defect expansion for Ovsienko--Redou data. -/
abbrev DefectExpansion
    {κ : Type _}
    [DecidableEq κ]
    (D : OvsienkoRedouData)
    (CalConf : Calculus Conf)
    (K : Finset κ) : Type _ :=
  PolyLaplacianCombinationData.PolyDefectExpansion
    (D.toPolyData CalConf) CalConf K

/-- Defect cancellation for Ovsienko--Redou data. -/
def SatisfiesDefectCancellation
    {κ : Type _}
    [DecidableEq κ]
    (D : OvsienkoRedouData)
    (CalConf : Calculus Conf)
    {K : Finset κ}
    (E : D.DefectExpansion CalConf K) : Prop :=
  PolyLaplacianCombinationData.SatisfiesDefectCancellation
    (D.toPolyData CalConf) CalConf E

/-- Defect cancellation implies bidifferential tangentiality. -/
theorem isBiTangential_of_defect_cancellation
    {κ : Type _}
    [DecidableEq κ]
    (D : OvsienkoRedouData)
    {K : Finset κ}
    (E : D.DefectExpansion CalConf K)
    (hcancel : D.SatisfiesDefectCancellation CalConf E) :
    CalConf.IsBiTangentialAtWeights
      (D.toOperator CalConf)
      D.w₁ D.w₂ := by
  unfold IsBiTangentialAtWeights
  change
    CalConf.IsTangentialAtWeights
      ((D.toPolyData CalConf).toOperator CalConf)
      (D.inputWeights CalConf)
  exact
    PolyLaplacianCombinationData.isTangentialAtWeights_of_defect_cancellation
      (CalConf := CalConf)
      (D.toPolyData CalConf)
      E hcancel

/-- Package an Ovsienko--Redou-style operator as a weighted bidifferential operator. -/
def toWeightedBiTangentialOperator
    (D : OvsienkoRedouData)
    (hmaps :
      CalConf.MapsWeights
        (D.toOperator CalConf)
        (D.inputWeights CalConf)
        D.outputWeight)
    (htangential :
      CalConf.IsBiTangentialAtWeights
        (D.toOperator CalConf)
        D.w₁ D.w₂) :
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
          (CalConf.biWeights D.w₁ D.w₂) := by
      exact htangential
    simpa [inputWeights] using ht hF hG hFG

/--
Full abstract construction from maps-weight data and defect cancellation.

The remaining paper-specific work is to instantiate `DefectExpansion` and prove
`SatisfiesDefectCancellation` from the Ovsienko--Redou coefficient recurrence.
-/
def construct
    {κ : Type _}
    [DecidableEq κ]
    (D : OvsienkoRedouData)
    {K : Finset κ}
    (E : D.DefectExpansion CalConf K)
    (hcancel : D.SatisfiesDefectCancellation CalConf E)
    (hmaps :
      CalConf.MapsWeights
        (D.toOperator CalConf)
        (D.inputWeights CalConf)
        D.outputWeight) :
    CalConf.WeightedBiTangentialOperator :=
  D.toWeightedBiTangentialOperator
    (CalConf := CalConf)
    hmaps
    (D.isBiTangential_of_defect_cancellation
      (CalConf := CalConf)
      E hcancel)

end OvsienkoRedouData

end Calculus
end Operators
end Ambient
end ConformalStructure
