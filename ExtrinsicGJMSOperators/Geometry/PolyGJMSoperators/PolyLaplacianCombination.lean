import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.LaplacianWords

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
# Rank-r finite combinations of Laplacian words

This is the rank-r framework behind both bidifferential and higher
polydifferential ambient operators.
-/

/-- A finite linear combination of rank-r Laplacian words of fixed total degree. -/
structure PolyLaplacianCombinationData (r : ℕ) where
  N : ℕ
  inputWeights : Fin r → ℝ
  support : Finset (LaplacianWord r)
  coeff : LaplacianWord r → ℝ
  support_totalPower :
    ∀ W ∈ support, W.totalPower = N

namespace PolyLaplacianCombinationData

/-- The expected output weight of a fixed-total-degree Laplacian combination. -/
def outputWeight
    {r : ℕ}
    (D : PolyLaplacianCombinationData r)
    (CalConf : Calculus Conf) : ℝ :=
  CalConf.outputWeight D.inputWeights D.N

/-- The rank-r multi-operator represented by a finite Laplacian-word sum. -/
def toOperator
    {r : ℕ}
    (D : PolyLaplacianCombinationData r)
    (CalConf : Calculus Conf) :
    CalConf.MultiOperator r :=
  CalConf.operatorSum D.support D.coeff
    (fun W => W.toOperator CalConf)

@[simp]
theorem toOperator_apply
    {r : ℕ}
    (D : PolyLaplacianCombinationData r)
    (F : CalConf.MultiInput r)
    (U : Conf.AmbientBundle) :
    D.toOperator CalConf F U =
      ∑ W ∈ D.support,
        D.coeff W * W.toOperator CalConf F U := by
  rfl

theorem expectedOutputWeight_eq_outputWeight_of_mem
    {r : ℕ}
    (D : PolyLaplacianCombinationData r)
    (CalConf : Calculus Conf)
    {W : LaplacianWord r}
    (hW : W ∈ D.support) :
    W.expectedOutputWeight CalConf D.inputWeights =
      D.outputWeight CalConf := by
  simp [LaplacianWord.expectedOutputWeight,
    PolyLaplacianCombinationData.outputWeight,
    Calculus.outputWeight,
    D.support_totalPower W hW]

/--
Abstract homogeneity of finite operator sums.

This isolates the extra `X`-linearity needed to prove that finite linear
combinations preserve output homogeneity.
-/
structure OperatorSumHomogeneityIdentities : Prop where
  operatorSum_mapsWeights :
    ∀ {r : ℕ} {ι : Type} [DecidableEq ι]
      (S : Finset ι)
      (c : ι → ℝ)
      (P : ι → CalConf.MultiOperator r)
      (w : Fin r → ℝ)
      (wout : ℝ),
      (∀ i ∈ S, CalConf.MapsWeights (P i) w wout) →
        CalConf.MapsWeights (CalConf.operatorSum S c P) w wout

/-- Weight mapping for fixed-total-degree Laplacian combinations. -/
theorem mapsWeights
    {r : ℕ}
    (D : PolyLaplacianCombinationData r)
    (H : CalConf.AlgebraicIdentities)
    (Hprod : CalConf.ProductHomogeneityIdentities)
    (Hsum : OperatorSumHomogeneityIdentities CalConf) :
    CalConf.MapsWeights
      (D.toOperator CalConf)
      D.inputWeights
      (D.outputWeight CalConf) := by
  unfold toOperator
  refine
    Hsum.operatorSum_mapsWeights
      D.support D.coeff (fun W : LaplacianWord r => W.toOperator CalConf)
      D.inputWeights (D.outputWeight CalConf) ?_
  intro W hW F hF
  rw [← D.expectedOutputWeight_eq_outputWeight_of_mem CalConf hW]
  exact (W.mapsWeights H Hprod D.inputWeights) hF

/--
Defect expansion for a rank-r Laplacian combination.

The field `combination_defect` says that the total output difference is
equivalent modulo `Q` to a linear combination of obstruction operators whose
coefficients are themselves the support-sums of word-level defect coefficients.
-/
structure PolyDefectExpansion
    {r : ℕ}
    {κ : Type _}
    [DecidableEq κ]
    (D : PolyLaplacianCombinationData r)
    (CalConf : Calculus Conf)
    (K : Finset κ) where
  obstruction : Fin r → κ → CalConf.MultiOperator r
  defectCoeff : LaplacianWord r → Fin r → κ → ℝ
  combination_defect :
    ∀ {F G : CalConf.MultiInput r},
      CalConf.IsMultiHomogeneous D.inputWeights F →
      CalConf.IsMultiHomogeneous D.inputWeights G →
      CalConf.SameBoundaryValueAtWeights D.inputWeights F G →
        CalConf.SameBoundaryValue
          (fun U => D.toOperator CalConf F U - D.toOperator CalConf G U)
          (fun U =>
            ∑ slot : Fin r,
              ∑ k ∈ K,
                (∑ W ∈ D.support, D.coeff W * defectCoeff W slot k)
                  * obstruction slot k F U)

/-- The obstruction coefficients cancel slot-by-slot. -/
def SatisfiesDefectCancellation
    {r : ℕ}
    {κ : Type _}
    [DecidableEq κ]
    (D : PolyLaplacianCombinationData r)
    (CalConf : Calculus Conf)
    {K : Finset κ}
    (E : PolyDefectExpansion D CalConf K) : Prop :=
  ∀ (slot : Fin r) (k : κ), k ∈ K →
    ∑ W ∈ D.support, D.coeff W * E.defectCoeff W slot k = 0

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

/--
If the total defect expansion has cancelling coefficients, the finite
Laplacian-word combination is tangential.
-/
theorem isTangentialAtWeights_of_defect_cancellation
    {r : ℕ}
    {κ : Type _}
    [DecidableEq κ]
    (D : PolyLaplacianCombinationData r)
    {K : Finset κ}
    (E : PolyDefectExpansion D CalConf K)
    (hcancel : SatisfiesDefectCancellation D CalConf E) :
    CalConf.IsTangentialAtWeights
      (D.toOperator CalConf)
      D.inputWeights := by
  intro F G hF hG hFG
  have hdef := E.combination_defect hF hG hFG
  let defectSum : Function Conf :=
    fun U =>
      ∑ slot : Fin r,
        ∑ k ∈ K,
          (∑ W ∈ D.support, D.coeff W * E.defectCoeff W slot k)
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

/-- Package a tangential fixed-degree combination as a weighted rank-r operator. -/
def toWeightedMultiTangentialOperator
    {r : ℕ}
    (D : PolyLaplacianCombinationData r)
    (hmaps :
      CalConf.MapsWeights
        (D.toOperator CalConf)
        D.inputWeights
        (D.outputWeight CalConf))
    (htangential :
      CalConf.IsTangentialAtWeights
        (D.toOperator CalConf)
        D.inputWeights) :
    CalConf.WeightedMultiTangentialOperator r where
  inputWeights := D.inputWeights
  outputWeight := D.outputWeight CalConf
  toOperator := D.toOperator CalConf
  mapsWeights := hmaps
  tangential := htangential

end PolyLaplacianCombinationData

end Calculus
end Operators
end Ambient
end ConformalStructure
