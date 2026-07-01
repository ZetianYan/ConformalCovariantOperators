import ConformalCovariantOperators.Ambient.PE.Renormalization.DivergenceVanishing

open Classical

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# The formal mechanism behind Theorem 1.4

The dimension `n` in the paper is the dimension of the PE manifold itself.
Accordingly, this file uses `X.bulkDim`, not `X.boundaryDim`.
-/

/-- Double factorial, with the convention `0!! = 1!! = 1`. -/
def doubleFactorial : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

theorem doubleFactorial_pos : forall n : Nat, 0 < doubleFactorial n
  | 0 => by simp [doubleFactorial]
  | 1 => by simp [doubleFactorial]
  | n + 2 => by
      simp [doubleFactorial, doubleFactorial_pos n]

theorem doubleFactorial_ne_zero (n : Nat) :
    doubleFactorial n ≠ 0 :=
  Nat.ne_of_gt (doubleFactorial_pos n)

/--
The PE specialization of the multiplier in Equation (3.2), at
`ell = n/2-k`.
-/
def criticalCaseMultiplierQ (n k : Nat) : Rat :=
  (2 : Rat) ^ (n / 2 - k)
    * (Nat.factorial (n / 2 - 1) : Rat)
    * (doubleFactorial (n - 2 * k - 1) : Rat)
    / (Nat.factorial (k - 1) : Rat)

/--
The coefficient in Theorem 1.4.

It is defined as the reciprocal of the explicit critical multiplier, avoiding
integer exponent coercions and truncated negative powers.
-/
def CaseCoeff (n k : Nat) : Real :=
  ((criticalCaseMultiplierQ n k : Rat) : Real)⁻¹

theorem criticalCaseMultiplierQ_pos (n k : Nat) :
    0 < criticalCaseMultiplierQ n k := by
  have hHalfFact : 0 < Nat.factorial (n / 2 - 1) :=
    Nat.factorial_pos _
  have hKFact : 0 < Nat.factorial (k - 1) :=
    Nat.factorial_pos _
  have hDouble : 0 < doubleFactorial (n - 2 * k - 1) :=
    doubleFactorial_pos _
  unfold criticalCaseMultiplierQ
  positivity

/-- The displayed Case coefficient is inverse to the recursion multiplier. -/
theorem CaseCoeff_mul_criticalCaseMultiplier (n k : Nat) :
    CaseCoeff n k
      * ((criticalCaseMultiplierQ n k : Rat) : Real)
      =
    1 := by
  have hQ : criticalCaseMultiplierQ n k ≠ 0 :=
    ne_of_gt (criticalCaseMultiplierQ_pos n k)
  have hR : ((criticalCaseMultiplierQ n k : Rat) : Real) ≠ 0 := by
    exact_mod_cast hQ
  exact inv_mul_cancel₀ hR

/-- Explicit nonnegative-power form of the coefficient in Theorem 1.4. -/
theorem CaseCoeff_eq_closedForm (n k : Nat) :
    CaseCoeff n k
      =
    (Nat.factorial (k - 1) : Real)
      /
    ((2 : Real) ^ (n / 2 - k)
      * (Nat.factorial (n / 2 - 1) : Real)
      * (doubleFactorial (n - 2 * k - 1) : Real)) := by
  have hMultiplier :
      ((criticalCaseMultiplierQ n k : Rat) : Real)
        =
      ((2 : Real) ^ (n / 2 - k)
        * (Nat.factorial (n / 2 - 1) : Real)
        * (doubleFactorial (n - 2 * k - 1) : Real))
        / (Nat.factorial (k - 1) : Real) := by
    simp [criticalCaseMultiplierQ]
  rw [CaseCoeff, hMultiplier]
  have hNumerator :
      (2 : Real) ^ (n / 2 - k)
        * (Nat.factorial (n / 2 - 1) : Real)
        * (doubleFactorial (n - 2 * k - 1) : Real)
        ≠ 0 := by
    have hDouble :
        (doubleFactorial (n - 2 * k - 1) : Real) ≠ 0 := by
      exact_mod_cast doubleFactorial_ne_zero (n - 2 * k - 1)
    positivity
  have hDenominator :
      (Nat.factorial (k - 1) : Real) ≠ 0 := by
    positivity
  field_simp

/--
Equation (3.2), specialized to a PE metric and the critical iterate, modulo
natural divergences.
-/
class CaseEinsteinEvaluationFormula
    [InvariantEvaluationModel] : Prop where
  critical_recursion_mod_divergence :
    forall
      (n k : Nat)
      (I : ScalarInvariant),
      1 <= k ->
      k <= n / 2 ->
      I.1.weight = -2 * (k : Int) ->
      InvariantEvaluationModel.EqualModuloDivergence
        (CaseLaplacianRecursion n k (n / 2 - k) I)
        (ScalarInvariant.qsmul (criticalCaseMultiplierQ n k) I)

/-- The critical ambient invariant `i^*(DeltaTilde^(n/2-k) Itilde)`. -/
def CaseCriticalInvariant
    (n k : Nat)
    (Itilde : AmbientScalarInvariant) :
    ScalarInvariant :=
  restrictToEinsteinSlice
    (ambientLaplacianIter (n / 2 - k) Itilde)

/--
The abstract integral identity underlying Theorem 1.4, expressed using the
renormalized functional in `PERenormalizationPackage`.
-/
theorem theorem_1_4_renormalizedIntegral
    (X : PESpace.{u, v})
    [InvariantEvaluationModel]
    [EinsteinAmbientLaplacianFormula]
    [CaseEinsteinEvaluationFormula]
    [P : PERenormalizationPackage X]
    (k : Nat)
    (I : ScalarInvariant)
    (Itilde : AmbientScalarInvariant)
    (hn : Even X.bulkDim)
    (hkpos : 1 <= k)
    (hkrange : k <= X.bulkDim / 2)
    (hStraight : ScalarStraightenable I Itilde)
    (hWeight : I.1.weight = -2 * (k : Int)) :
    P.RInt I
      =
    CaseCoeff X.bulkDim k
      * P.convergentIntegral
          (CaseCriticalInvariant X.bulkDim k Itilde) := by
  let n := X.bulkDim
  let ell := n / 2 - k
  let Iell := CaseLaplacianRecursion n k ell I
  let ItildeEll := ambientLaplacianIter ell Itilde
  let Icritical := restrictToEinsteinSlice ItildeEll

  have hStraightEll : ScalarStraightenable Iell ItildeEll := by
    exact straightenable_laplacian_iterate
      n k ell I Itilde hStraight hWeight

  have hnHalf : 2 * (n / 2) = n := by
    rcases hn with ⟨m, hm⟩
    omega

  have hCriticalBase : Iell.1.weight = -(n : Int) := by
    rw [show Iell.1.weight = I.1.weight - 2 * (ell : Int) by
      exact CaseLaplacianRecursion_weight n k ell I]
    rw [hWeight]
    dsimp [ell]
    rw [Nat.cast_sub hkrange]
    push_cast
    omega

  have hItildeWeight : Itilde.1.weight = -2 * (k : Int) := by
    change Straightenable I.1 Itilde.1 at hStraight
    rw [← hStraight.weight_eq]
    exact hWeight

  have hCriticalAmbient :
      Itilde.1.weight - 2 * (ell : Int) = -(n : Int) := by
    rw [hItildeWeight]
    dsimp [ell]
    rw [Nat.cast_sub hkrange]
    push_cast
    omega

  have hConformal : IsScalarConformalInvariant Icritical := by
    exact ambient_laplacian_iter_einstein_slice_conformal
      n ell Itilde hCriticalAmbient

  have hAssociatedIntegral :
      P.RInt Iell = P.RInt Icritical := by
    exact P.associated_integral_eq Iell ItildeEll hStraightEll

  have hCriticalConverges :
      P.RInt Icritical = P.convergentIntegral Icritical := by
    exact P.critical_weight_converges
      Icritical
      (by
        change ItildeEll.1.weight = -(n : Int)
        rw [ambientLaplacianIter_weight]
        exact hCriticalAmbient)
      hConformal

  have hModulo :
      InvariantEvaluationModel.EqualModuloDivergence
        Iell
        (ScalarInvariant.qsmul (criticalCaseMultiplierQ n k) I) := by
    exact CaseEinsteinEvaluationFormula.critical_recursion_mod_divergence
      n k I hkpos hkrange hWeight

  have hRecursionIntegral :
      P.RInt Iell
        =
      ((criticalCaseMultiplierQ n k : Rat) : Real) * P.RInt I := by
    calc
      P.RInt Iell
          = P.RInt
              (ScalarInvariant.qsmul (criticalCaseMultiplierQ n k) I) :=
            P.moduloDivergence_eq _ _ hModulo
      _ = ((criticalCaseMultiplierQ n k : Rat) : Real) * P.RInt I :=
            P.linear_qsmul _ I

  calc
    P.RInt I = 1 * P.RInt I := by ring
    _ = (CaseCoeff n k
          * ((criticalCaseMultiplierQ n k : Rat) : Real)) * P.RInt I := by
          rw [CaseCoeff_mul_criticalCaseMultiplier]
    _ = CaseCoeff n k
          * (((criticalCaseMultiplierQ n k : Rat) : Real) * P.RInt I) := by
          ring
    _ = CaseCoeff n k * P.RInt Iell := by
          rw [hRecursionIntegral]
    _ = CaseCoeff n k * P.RInt Icritical := by
          rw [hAssociatedIntegral]
    _ = CaseCoeff n k * P.convergentIntegral Icritical := by
          rw [hCriticalConverges]

/--
Theorem 1.4 with the left-hand side written as the Phase B finite-part
renormalized curvature integral.
-/
theorem theorem_1_4_formal
    (X : PESpace.{u, v})
    [InvariantEvaluationModel]
    [EinsteinAmbientLaplacianFormula]
    [CaseEinsteinEvaluationFormula]
    [P : PERenormalizationPackage X]
    (k : Nat)
    (I : ScalarInvariant)
    (Itilde : AmbientScalarInvariant)
    (hn : Even X.bulkDim)
    (hkpos : 1 <= k)
    (hkrange : k <= X.bulkDim / 2)
    (hStraight : ScalarStraightenable I Itilde)
    (hWeight : I.1.weight = -2 * (k : Int)) :
    RenormalizedCurvatureIntegral (P.cutoffData I)
      =
    CaseCoeff X.bulkDim k
      * P.convergentIntegral
          (CaseCriticalInvariant X.bulkDim k Itilde) := by
  rw [← P.RInt_eq_phaseB I]
  exact theorem_1_4_renormalizedIntegral
    X k I Itilde hn hkpos hkrange hStraight hWeight

end PE
end Ambient
end ConformalStructure
