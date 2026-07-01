import ConformalCovariantOperators.Ambient.PE.Invariants.LaplacianRecursion

open Classical

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Pfaffian-like Weyl invariants

The generalized Kronecker-delta contraction is represented by the `pfLike`
syntax constructor.  A concrete tensor backend can later interpret it.
-/

/-- The scalar invariant `Pf_ell(W)`. -/
def WeylPfLike (ell : Nat) : ScalarInvariant :=
  ⟨
    {
      expr :=
        TensorInvariantExpr.pfLike ell WeylTensorInvariant.expr
      rank := 0
      weight := -2 * (ell : Int)
      parity := InvariantParity.even
    },
    rfl
  ⟩

/-- The corresponding ambient invariant `Pf_ell(RmTilde)`. -/
def AmbientRmPfLike (ell : Nat) : AmbientScalarInvariant :=
  ⟨
    {
      expr :=
        TensorInvariantExpr.pfLike ell AmbientRiemannTensorInvariant.expr
      rank := 0
      weight := -2 * (ell : Int)
      parity := InvariantParity.even
    },
    rfl
  ⟩

@[simp]
theorem WeylPfLike_weight (ell : Nat) :
    (WeylPfLike ell).1.weight = -2 * (ell : Int) := by
  rfl

@[simp]
theorem AmbientRmPfLike_weight (ell : Nat) :
    (AmbientRmPfLike ell).1.weight = -2 * (ell : Int) := by
  rfl

/-- Semantic input that the alternating complete contraction preserves association. -/
class PfLikeStraightness
    [InvariantEvaluationModel] : Prop where
  associated :
    forall ell : Nat,
      InvariantEvaluationModel.Associated
        (WeylPfLike ell).1
        (AmbientRmPfLike ell).1

/-- Pfaffian-like Weyl polynomials are straightenable. -/
theorem WeylPfLike_straightenable
    [InvariantEvaluationModel]
    [PfLikeStraightness]
    (ell : Nat) :
    ScalarStraightenable (WeylPfLike ell) (AmbientRmPfLike ell) := by
  exact ⟨rfl, rfl, PfLikeStraightness.associated ell⟩

/--
The scalar conformal invariant

`P_(ell,n) = i^*(DeltaTilde^(n/2-ell) Pf_ell(RmTilde))`.
-/
def P_l_n (ell n : Nat) : ScalarInvariant :=
  restrictToEinsteinSlice
    (ambientLaplacianIter
      (n / 2 - ell)
      (AmbientRmPfLike ell))

theorem P_l_n_weight
    (ell n : Nat)
    (hn : Even n)
    (hRange : ell <= n / 2) :
    (P_l_n ell n).1.weight = -(n : Int) := by
  change
    (ambientLaplacianIter
      (n / 2 - ell)
      (AmbientRmPfLike ell)).1.weight
      =
    -(n : Int)
  rw [ambientLaplacianIter_weight, AmbientRmPfLike_weight]
  rw [Nat.cast_sub hRange]
  push_cast
  rcases hn with ⟨m, hm⟩
  have hnHalf : 2 * (n / 2) = n := by
    omega
  omega

theorem P_l_n_conformal
    [InvariantEvaluationModel]
    [EinsteinAmbientLaplacianFormula]
    (ell n : Nat)
    (hn : Even n)
    (hRange : ell <= n / 2) :
    IsScalarConformalInvariant (P_l_n ell n) := by
  apply ambient_laplacian_iter_einstein_slice_conformal
    n (n / 2 - ell) (AmbientRmPfLike ell)
  rw [AmbientRmPfLike_weight, Nat.cast_sub hRange]
  push_cast
  rcases hn with ⟨m, hm⟩
  have hnHalf : 2 * (n / 2) = n := by
    omega
  omega

/-- The full Pfaffian in even formal dimension `n`. -/
def FullPfaffianInvariant (n : Nat) : ScalarInvariant :=
  ⟨
    {
      expr :=
        TensorInvariantExpr.pfLike (n / 2) TensorInvariantExpr.riem
      rank := 0
      weight := -(n : Int)
      parity := InvariantParity.even
    },
    rfl
  ⟩

end PE
end Ambient
end ConformalStructure
