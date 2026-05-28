import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.Tangential

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
# Finite linear combinations of rank-r ambient operators

This file keeps the combination layer abstract: it only knows about rank-r
multi-operators and boundary equivalence. Weight mapping for sums needs extra
linearity of `X`, so it is deliberately left to a later algebraic layer.
-/

/-- A single scalar multiple of a rank-r operator. -/
def singleOperator
    {r : ℕ}
    (c : ℝ)
    (P : CalConf.MultiOperator r) :
    CalConf.MultiOperator r :=
  CalConf.multiSmul c P

/-- A finite linear combination of rank-r operators. -/
def operatorSum
    {r : ℕ}
    {ι : Type _}
    [DecidableEq ι]
    (S : Finset ι)
    (c : ι → ℝ)
    (P : ι → CalConf.MultiOperator r) :
    CalConf.MultiOperator r :=
  fun F U => ∑ i ∈ S, c i * P i F U

@[simp]
theorem singleOperator_apply
    {r : ℕ}
    (c : ℝ)
    (P : CalConf.MultiOperator r)
    (F : CalConf.MultiInput r)
    (U : Conf.AmbientBundle) :
    CalConf.singleOperator c P F U = c * P F U := by
  rfl

@[simp]
theorem operatorSum_apply
    {r : ℕ}
    {ι : Type _}
    [DecidableEq ι]
    (S : Finset ι)
    (c : ι → ℝ)
    (P : ι → CalConf.MultiOperator r)
    (F : CalConf.MultiInput r)
    (U : Conf.AmbientBundle) :
    CalConf.operatorSum S c P F U = ∑ i ∈ S, c i * P i F U := by
  rfl

@[simp]
theorem operatorSum_empty
    {r : ℕ}
    {ι : Type _}
    [DecidableEq ι]
    (c : ι → ℝ)
    (P : ι → CalConf.MultiOperator r) :
    CalConf.operatorSum (∅ : Finset ι) c P = CalConf.multiZero r := by
  funext F U
  simp [operatorSum, multiZero, zero]

@[simp]
theorem operatorSum_singleton
    {r : ℕ}
    {ι : Type _}
    [DecidableEq ι]
    (i : ι)
    (c : ι → ℝ)
    (P : ι → CalConf.MultiOperator r) :
    CalConf.operatorSum ({i} : Finset ι) c P =
      CalConf.singleOperator (c i) (P i) := by
  funext F U
  simp [operatorSum, singleOperator, multiSmul]

/-- Boundary equivalence is stable under finite sums. -/
theorem SameBoundaryValue_finset_sum
    {ι : Type _}
    [DecidableEq ι]
    (S : Finset ι)
    (A B : ι → Function Conf)
    (hAB : ∀ i ∈ S, CalConf.SameBoundaryValue (A i) (B i)) :
    CalConf.SameBoundaryValue
      (fun U => ∑ i ∈ S, A i U)
      (fun U => ∑ i ∈ S, B i U) := by
  classical
  revert hAB
  refine Finset.induction_on S ?base ?step
  · intro _hAB
    simpa using CalConf.SameBoundaryValue_refl (fun _ : Conf.AmbientBundle => 0)
  · intro a S ha ih hAB
    have haAB : CalConf.SameBoundaryValue (A a) (B a) := by
      exact hAB a (by simp)
    have hSAB :
        CalConf.SameBoundaryValue
          (fun U => ∑ i ∈ S, A i U)
          (fun U => ∑ i ∈ S, B i U) := by
      apply ih
      intro i hi
      exact hAB i (by simp [hi])
    have hadd := CalConf.SameBoundaryValue_add haAB hSAB
    simpa [Finset.sum_insert ha, add] using hadd

namespace IsTangentialAtWeights

variable {CalConf}

/-- A finite linear combination of tangential operators is tangential. -/
theorem operatorSum
    {r : ℕ}
    {ι : Type _}
    [DecidableEq ι]
    (S : Finset ι)
    (c : ι → ℝ)
    (P : ι → CalConf.MultiOperator r)
    {w : Fin r → ℝ}
    (hP : ∀ i ∈ S, CalConf.IsTangentialAtWeights (P i) w) :
    CalConf.IsTangentialAtWeights (CalConf.operatorSum S c P) w := by
  intro F G hF hG hFG
  have hsum :
      CalConf.SameBoundaryValue
        (fun U => ∑ i ∈ S, c i * P i F U)
        (fun U => ∑ i ∈ S, c i * P i G U) := by
    apply CalConf.SameBoundaryValue_finset_sum
    intro i hi
    have hiTangential := hP i hi hF hG hFG
    simpa [smul] using CalConf.SameBoundaryValue_smul (c i) hiTangential
  simpa [operatorSum] using hsum

end IsTangentialAtWeights

end Calculus
end Operators
end Ambient
end ConformalStructure
