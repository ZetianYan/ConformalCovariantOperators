import ConformalCovariantOperators.Ambient.PE.Invariants.RiemannianInvariant

open Classical

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Straight and straightenable invariants

The semantic relation is supplied by `InvariantEvaluationModel`.  This keeps
the symbolic calculus independent of a future concrete tensor evaluator while
still making closure theorems honest consequences of explicit model laws.
-/

/-- Evaluation laws needed by the symbolic invariant calculus. -/
class InvariantEvaluationModel where
  /-- Association on canonical straight ambient spaces of Einstein metrics. -/
  Associated : TensorInvariant -> AmbientInvariant -> Prop
  /-- Semantic naturality predicate. -/
  IsNatural : TensorInvariant -> Prop
  /-- Semantic conformal-covariance predicate for scalar invariants. -/
  IsScalarConformal : ScalarInvariant -> Prop
  /-- Equality modulo a natural divergence. -/
  EqualModuloDivergence : ScalarInvariant -> ScalarInvariant -> Prop
  /-- Contraction with the ambient dilation field in the last index vanishes. -/
  XAnnihilatesLastIndex : AmbientInvariant -> Prop
  associated_one :
    Associated scalarOne.1 ambientScalarOne.1
  associated_tensorProd :
    forall {S T : TensorInvariant} {St Tt : AmbientInvariant},
      Associated S St ->
      Associated T Tt ->
      Associated
        (tensorProdInvariant S T)
        (ambientTensorProdInvariant St Tt)
  associated_contract :
    forall {T : TensorInvariant} {Tt : AmbientInvariant},
      Associated T Tt ->
      forall C : IndexPairing,
        Associated
          (contractInvariant T C)
          (ambientContractInvariant Tt C)

/-- Semantic naturality in the selected evaluation model. -/
def IsNaturalInvariant
    [InvariantEvaluationModel]
    (I : TensorInvariant) :
    Prop :=
  InvariantEvaluationModel.IsNatural I

/-- Scalar conformal covariance in the selected evaluation model. -/
def IsScalarConformalInvariant
    [InvariantEvaluationModel]
    (I : ScalarInvariant) :
    Prop :=
  InvariantEvaluationModel.IsScalarConformal I

/-- A base invariant associated to a straight ambient invariant. -/
structure Straightenable
    [InvariantEvaluationModel]
    (I : TensorInvariant)
    (Itilde : AmbientInvariant) : Prop where
  rank_eq : I.rank = Itilde.rank
  weight_eq : I.weight = Itilde.weight
  eval_on_einstein_ambient :
    InvariantEvaluationModel.Associated I Itilde

/-- Scalar specialization of straightenable invariants. -/
def ScalarStraightenable
    [InvariantEvaluationModel]
    (I : ScalarInvariant)
    (Itilde : AmbientScalarInvariant) :
    Prop :=
  Straightenable I.1 Itilde.1

theorem straightenable_one
    [InvariantEvaluationModel] :
    ScalarStraightenable scalarOne ambientScalarOne := by
  refine ⟨rfl, rfl, ?_⟩
  exact InvariantEvaluationModel.associated_one

/-- Tensor products preserve straightenable association. -/
theorem straightenable_tensorProd
    [InvariantEvaluationModel]
    {S T : TensorInvariant}
    {St Tt : AmbientInvariant}
    (hS : Straightenable S St)
    (hT : Straightenable T Tt) :
    Straightenable
      (tensorProdInvariant S T)
      (ambientTensorProdInvariant St Tt) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [tensorProdInvariant, ambientTensorProdInvariant, hS.rank_eq, hT.rank_eq]
  · simp [tensorProdInvariant, ambientTensorProdInvariant, hS.weight_eq, hT.weight_eq]
  · exact InvariantEvaluationModel.associated_tensorProd
      hS.eval_on_einstein_ambient hT.eval_on_einstein_ambient

/-- Partial contractions preserve straightenable association. -/
theorem straightenable_contract
    [InvariantEvaluationModel]
    {T : TensorInvariant}
    {Tt : AmbientInvariant}
    (hT : Straightenable T Tt)
    (C : IndexPairing) :
    Straightenable
      (contractInvariant T C)
      (ambientContractInvariant Tt C) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [contractInvariant, ambientContractInvariant, hT.rank_eq]
  · simp [contractInvariant, ambientContractInvariant, hT.weight_eq]
  · exact InvariantEvaluationModel.associated_contract
      hT.eval_on_einstein_ambient C

/-- The Weyl tensor as a rank-four invariant of weight two. -/
def WeylTensorInvariant : TensorInvariant where
  expr := TensorInvariantExpr.riem
  rank := 4
  weight := 2
  parity := InvariantParity.even

/-- The ambient Riemann tensor as a rank-four invariant of weight two. -/
def AmbientRiemannTensorInvariant : AmbientInvariant where
  expr := TensorInvariantExpr.riem
  rank := 4
  weight := 2
  parity := InvariantParity.even

/-- The semantic input corresponding to Lemma 3.4. -/
class WeylAmbientStraightness
    [InvariantEvaluationModel] : Prop where
  associated :
    InvariantEvaluationModel.Associated
      WeylTensorInvariant
      AmbientRiemannTensorInvariant

/-- Lemma 3.4: Weyl is associated to ambient Riemann curvature. -/
theorem Weyl_straightenable_AmbientRm
    [InvariantEvaluationModel]
    [WeylAmbientStraightness] :
    Straightenable WeylTensorInvariant AmbientRiemannTensorInvariant := by
  exact ⟨rfl, rfl, WeylAmbientStraightness.associated⟩

/-- Tensor power of the Weyl invariant. -/
def weylPower : Nat -> TensorInvariant
  | 0 => scalarOne.1
  | k + 1 => tensorProdInvariant (weylPower k) WeylTensorInvariant

/-- Tensor power of ambient Riemann curvature. -/
def ambientRiemannPower : Nat -> AmbientInvariant
  | 0 => ambientScalarOne.1
  | k + 1 =>
      ambientTensorProdInvariant
        (ambientRiemannPower k)
        AmbientRiemannTensorInvariant

@[simp]
theorem weylPower_rank (k : Nat) :
    (weylPower k).rank = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [weylPower, tensorProdInvariant, WeylTensorInvariant, ih]
      omega

@[simp]
theorem weylPower_weight (k : Nat) :
    (weylPower k).weight = 2 * (k : Int) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [weylPower, tensorProdInvariant, WeylTensorInvariant, ih]
      omega

@[simp]
theorem ambientRiemannPower_rank (k : Nat) :
    (ambientRiemannPower k).rank = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [
        ambientRiemannPower,
        ambientTensorProdInvariant,
        AmbientRiemannTensorInvariant,
        ih
      ]
      omega

@[simp]
theorem ambientRiemannPower_weight (k : Nat) :
    (ambientRiemannPower k).weight = 2 * (k : Int) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [
        ambientRiemannPower,
        ambientTensorProdInvariant,
        AmbientRiemannTensorInvariant,
        ih
      ]
      omega

theorem weylPower_straightenable
    [InvariantEvaluationModel]
    [WeylAmbientStraightness]
    (k : Nat) :
    Straightenable (weylPower k) (ambientRiemannPower k) := by
  induction k with
  | zero =>
      exact straightenable_one
  | succ k ih =>
      exact straightenable_tensorProd ih Weyl_straightenable_AmbientRm

/-- A complete contraction of a rank-`r` tensor. -/
structure CompleteContraction (r : Nat) where
  pairing : IndexPairing
  complete : 2 * pairing.pairCount = r

/-- A complete contraction of `W` to a scalar invariant. -/
def WeylCompleteContraction
    (k : Nat)
    (C : CompleteContraction (4 * k)) :
    ScalarInvariant := by
  refine ⟨contractInvariant (weylPower k) C.pairing, ?_⟩
  change (weylPower k).rank - 2 * C.pairing.pairCount = 0
  rw [weylPower_rank]
  have hcomplete := C.complete
  omega

/-- The corresponding complete contraction of ambient Riemann curvature. -/
def AmbientRmCompleteContraction
    (k : Nat)
    (C : CompleteContraction (4 * k)) :
    AmbientScalarInvariant := by
  refine ⟨ambientContractInvariant (ambientRiemannPower k) C.pairing, ?_⟩
  change (ambientRiemannPower k).rank - 2 * C.pairing.pairCount = 0
  rw [ambientRiemannPower_rank]
  have hcomplete := C.complete
  omega

@[simp]
theorem WeylCompleteContraction_weight
    (k : Nat)
    (C : CompleteContraction (4 * k)) :
    (WeylCompleteContraction k C).1.weight = -2 * (k : Int) := by
  change (weylPower k).weight - 2 * (C.pairing.pairCount : Int)
      = -2 * (k : Int)
  rw [weylPower_weight]
  have hcomplete :
      (2 * C.pairing.pairCount : Int) = 4 * (k : Int) := by
    exact_mod_cast C.complete
  omega

/-- Corollary 3.6: complete Weyl contractions are straightenable. -/
theorem WeylPolynomial_straightenable
    [InvariantEvaluationModel]
    [WeylAmbientStraightness]
    (k : Nat)
    (C : CompleteContraction (4 * k)) :
    ScalarStraightenable
      (WeylCompleteContraction k C)
      (AmbientRmCompleteContraction k C) := by
  exact straightenable_contract (weylPower_straightenable k) C.pairing

end PE
end Ambient
end ConformalStructure
