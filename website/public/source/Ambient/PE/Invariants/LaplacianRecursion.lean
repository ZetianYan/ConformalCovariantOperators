import ConformalCovariantOperators.Ambient.PE.Invariants.Straightenable

open Classical

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Ambient Laplacian recursion

This file formalizes the inductive mechanism of Proposition 3.7.  The
Einstein ambient Laplacian identity is an explicit model law; the iteration and
all weight bookkeeping are proved here.
-/

/--
Coefficient

`4 (k+j) (n-2k-2j-1) / n`

in the `j`-th Case Laplacian factor.  The signed numerator is formed in `Int`
before coercion to `Rat`.
-/
def caseLaplacianCoefficient (n k j : Nat) : Rat :=
  (4 : Rat)
    * (k + j : Nat)
    * (((n : Int) - 2 * (k : Int) - 2 * (j : Int) - 1 : Int) : Rat)
    / (n : Rat)

/-- One factor in Equation (3.1). -/
def CaseLaplacianFactor
    (n k j : Nat)
    (I : ScalarInvariant) :
    ScalarInvariant :=
  ⟨
    {
      expr :=
        TensorInvariantExpr.add
          (TensorInvariantExpr.laplacian I.1.expr)
          (TensorInvariantExpr.scalarMul
            (-caseLaplacianCoefficient n k j)
            (TensorInvariantExpr.jMul I.1.expr))
      rank := 0
      weight := I.1.weight - 2
      parity := I.1.parity
    },
    rfl
  ⟩

@[simp]
theorem CaseLaplacianFactor_weight
    (n k j : Nat)
    (I : ScalarInvariant) :
    (CaseLaplacianFactor n k j I).1.weight = I.1.weight - 2 := by
  rfl

/-- Iteration of Equation (3.1), ordered by increasing `j`. -/
def CaseLaplacianRecursion
    (n k : Nat) :
    Nat -> ScalarInvariant -> ScalarInvariant
  | 0, I => I
  | ell + 1, I =>
      CaseLaplacianFactor n k ell
        (CaseLaplacianRecursion n k ell I)

@[simp]
theorem CaseLaplacianRecursion_zero
    (n k : Nat)
    (I : ScalarInvariant) :
    CaseLaplacianRecursion n k 0 I = I := by
  rfl

@[simp]
theorem CaseLaplacianRecursion_succ
    (n k ell : Nat)
    (I : ScalarInvariant) :
    CaseLaplacianRecursion n k (ell + 1) I
      =
    CaseLaplacianFactor n k ell
      (CaseLaplacianRecursion n k ell I) := by
  rfl

/-- Every recursion step lowers weight by two. -/
theorem CaseLaplacianRecursion_weight
    (n k ell : Nat)
    (I : ScalarInvariant) :
    (CaseLaplacianRecursion n k ell I).1.weight
      =
    I.1.weight - 2 * (ell : Int) := by
  induction ell with
  | zero =>
      simp
  | succ ell ih =>
      rw [CaseLaplacianRecursion_succ, CaseLaplacianFactor_weight, ih]
      push_cast
      ring

/-- Iterated ambient Laplacian. -/
def ambientLaplacianIter :
    Nat -> AmbientScalarInvariant -> AmbientScalarInvariant
  | 0, I => I
  | ell + 1, I =>
      AmbientScalarInvariant.laplacian
        (ambientLaplacianIter ell I)

@[simp]
theorem ambientLaplacianIter_zero
    (I : AmbientScalarInvariant) :
    ambientLaplacianIter 0 I = I := by
  rfl

@[simp]
theorem ambientLaplacianIter_succ
    (ell : Nat)
    (I : AmbientScalarInvariant) :
    ambientLaplacianIter (ell + 1) I
      =
    AmbientScalarInvariant.laplacian
      (ambientLaplacianIter ell I) := by
  rfl

theorem ambientLaplacianIter_weight
    (ell : Nat)
    (I : AmbientScalarInvariant) :
    (ambientLaplacianIter ell I).1.weight
      =
    I.1.weight - 2 * (ell : Int) := by
  induction ell with
  | zero =>
      simp
  | succ ell ih =>
      rw [ambientLaplacianIter_succ]
      change
        (ambientLaplacianIter ell I).1.weight - 2
          =
        I.1.weight - 2 * ((ell + 1 : Nat) : Int)
      rw [ih]
      push_cast
      ring

/--
Semantic form of the weighted-pullback ambient Laplacian identity used in
Proposition 3.7.
-/
class EinsteinAmbientLaplacianFormula
    [InvariantEvaluationModel] where
  associated_step :
    forall
      (n k j : Nat)
      (I : ScalarInvariant)
      (Itilde : AmbientScalarInvariant),
      ScalarStraightenable I Itilde ->
      I.1.weight = -2 * ((k + j : Nat) : Int) ->
      InvariantEvaluationModel.Associated
        (CaseLaplacianFactor n k j I).1
        (AmbientScalarInvariant.laplacian Itilde).1
  critical_slice_conformal :
    forall (n : Nat) (Itilde : AmbientScalarInvariant),
      Itilde.1.weight = -(n : Int) ->
      IsScalarConformalInvariant (restrictToEinsteinSlice Itilde)

/-- One application of the ambient Laplacian preserves association. -/
theorem straightenable_laplacian_step
    [InvariantEvaluationModel]
    [EinsteinAmbientLaplacianFormula]
    (n k j : Nat)
    (I : ScalarInvariant)
    (Itilde : AmbientScalarInvariant)
    (hStraight : ScalarStraightenable I Itilde)
    (hWeight : I.1.weight = -2 * ((k + j : Nat) : Int)) :
    ScalarStraightenable
      (CaseLaplacianFactor n k j I)
      (AmbientScalarInvariant.laplacian Itilde) := by
  change Straightenable I.1 Itilde.1 at hStraight
  refine ⟨rfl, ?_, ?_⟩
  · change I.1.weight - 2 = Itilde.1.weight - 2
    rw [hStraight.weight_eq]
  · exact EinsteinAmbientLaplacianFormula.associated_step
      n k j I Itilde hStraight hWeight

/--
Proposition 3.7: the recursive base invariant is associated to the iterated
ambient Laplacian.
-/
theorem straightenable_laplacian_iterate
    [InvariantEvaluationModel]
    [EinsteinAmbientLaplacianFormula]
    (n k ell : Nat)
    (I : ScalarInvariant)
    (Itilde : AmbientScalarInvariant)
    (hStraight : ScalarStraightenable I Itilde)
    (hWeight : I.1.weight = -2 * (k : Int)) :
    ScalarStraightenable
      (CaseLaplacianRecursion n k ell I)
      (ambientLaplacianIter ell Itilde) := by
  induction ell with
  | zero =>
      simpa using hStraight
  | succ ell ih =>
      rw [CaseLaplacianRecursion_succ, ambientLaplacianIter_succ]
      apply straightenable_laplacian_step n k ell
      · exact ih
      · rw [CaseLaplacianRecursion_weight, hWeight]
        push_cast
        ring

/--
At critical weight, restriction of the ambient iterate to the Einstein slice
is a scalar conformal invariant.
-/
theorem ambient_laplacian_iter_einstein_slice_conformal
    [InvariantEvaluationModel]
    [EinsteinAmbientLaplacianFormula]
    (n ell : Nat)
    (Itilde : AmbientScalarInvariant)
    (hCritical :
      Itilde.1.weight - 2 * (ell : Int) = -(n : Int)) :
    IsScalarConformalInvariant
      (restrictToEinsteinSlice (ambientLaplacianIter ell Itilde)) := by
  apply EinsteinAmbientLaplacianFormula.critical_slice_conformal n
  rw [ambientLaplacianIter_weight]
  exact hCritical

end PE
end Ambient
end ConformalStructure
