import Mathlib

open Classical

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Symbolic Riemannian invariants

This file implements the rank and weight bookkeeping used in Case--Khaitan--
Lin--Tyrrell--Yuan.  The expression language is intentionally independent of a
concrete tensor-calculus backend.
-/

/-- Orientation parity of a symbolic invariant. -/
inductive InvariantParity where
  | even
  | odd
  | mixed
deriving Repr, DecidableEq

namespace InvariantParity

/-- Parity of a tensor product. -/
def tensorProduct : InvariantParity -> InvariantParity -> InvariantParity
  | even, p => p
  | p, even => p
  | odd, odd => even
  | mixed, _ => mixed
  | _, mixed => mixed

end InvariantParity

/-- Symbolic data describing a partial contraction of tensor indices. -/
structure IndexPairing where
  pairs : List (Nat × Nat)
  /-- Later backends can require disjoint valid index pairs. -/
  validity : Prop

namespace IndexPairing

/-- Number of contracted index pairs. -/
def pairCount (C : IndexPairing) : Nat :=
  C.pairs.length

end IndexPairing

/-- Syntax for natural tensor invariants and the operations used in the paper. -/
inductive TensorInvariantExpr where
  | constOne
  | metric
  | invMetric
  | riem
  | covDerivRiem (order : Nat)
  | tensorProd (A B : TensorInvariantExpr)
  | contract (A : TensorInvariantExpr) (C : IndexPairing)
  | linComb (terms : List (Rat × TensorInvariantExpr))
  | scalarMul (c : Rat) (A : TensorInvariantExpr)
  | add (A B : TensorInvariantExpr)
  | laplacian (A : TensorInvariantExpr)
  | jMul (A : TensorInvariantExpr)
  | divergence (A : TensorInvariantExpr)
  | ambientLaplacian (A : TensorInvariantExpr)
  | restrictAmbient (A : TensorInvariantExpr)
  | pfLike (order : Nat) (A : TensorInvariantExpr)

/-- A base Riemannian invariant with formal metadata. -/
structure TensorInvariant where
  expr : TensorInvariantExpr
  rank : Nat
  weight : Int
  parity : InvariantParity

/-- An ambient Riemannian invariant with formal metadata. -/
structure AmbientInvariant where
  expr : TensorInvariantExpr
  rank : Nat
  weight : Int
  parity : InvariantParity

/-- Scalar base invariants. -/
abbrev ScalarInvariant :=
  {I : TensorInvariant // I.rank = 0}

/-- Rank-one base invariants. -/
abbrev OneFormInvariant :=
  {I : TensorInvariant // I.rank = 1}

/-- Scalar ambient invariants. -/
abbrev AmbientScalarInvariant :=
  {I : AmbientInvariant // I.rank = 0}

/-- Rank-one ambient invariants. -/
abbrev AmbientOneFormInvariant :=
  {I : AmbientInvariant // I.rank = 1}

/-- Tensor weight `weight - rank`, invariant under contractions. -/
def tensorWeight (I : TensorInvariant) : Int :=
  I.weight - I.rank

/-- Ambient tensor weight `weight - rank`. -/
def ambientTensorWeight (I : AmbientInvariant) : Int :=
  I.weight - I.rank

/-- The constant scalar invariant `1`. -/
def scalarOne : ScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.constOne
      rank := 0
      weight := 0
      parity := InvariantParity.even
    },
    rfl
  ⟩

/-- The constant ambient scalar invariant `1`. -/
def ambientScalarOne : AmbientScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.constOne
      rank := 0
      weight := 0
      parity := InvariantParity.even
    },
    rfl
  ⟩

/-- Tensor product of base invariants. -/
def tensorProdInvariant
    (S T : TensorInvariant) :
    TensorInvariant where
  expr := TensorInvariantExpr.tensorProd S.expr T.expr
  rank := S.rank + T.rank
  weight := S.weight + T.weight
  parity := InvariantParity.tensorProduct S.parity T.parity

/-- Tensor product of ambient invariants. -/
def ambientTensorProdInvariant
    (S T : AmbientInvariant) :
    AmbientInvariant where
  expr := TensorInvariantExpr.tensorProd S.expr T.expr
  rank := S.rank + T.rank
  weight := S.weight + T.weight
  parity := InvariantParity.tensorProduct S.parity T.parity

/--
Partial contraction of a base tensor.

Every contracted pair lowers both rank and metric weight by two, preserving
tensor weight when enough indices are present.
-/
def contractInvariant
    (T : TensorInvariant)
    (C : IndexPairing) :
    TensorInvariant where
  expr := TensorInvariantExpr.contract T.expr C
  rank := T.rank - 2 * C.pairCount
  weight := T.weight - 2 * C.pairCount
  parity := T.parity

/-- Partial contraction of an ambient tensor. -/
def ambientContractInvariant
    (T : AmbientInvariant)
    (C : IndexPairing) :
    AmbientInvariant where
  expr := TensorInvariantExpr.contract T.expr C
  rank := T.rank - 2 * C.pairCount
  weight := T.weight - 2 * C.pairCount
  parity := T.parity

theorem tensorWeight_contractInvariant
    (T : TensorInvariant)
    (C : IndexPairing)
    (hC : 2 * C.pairCount <= T.rank) :
    tensorWeight (contractInvariant T C) = tensorWeight T := by
  simp only [tensorWeight, contractInvariant]
  rw [Nat.cast_sub hC]
  push_cast
  ring

theorem ambientTensorWeight_contractInvariant
    (T : AmbientInvariant)
    (C : IndexPairing)
    (hC : 2 * C.pairCount <= T.rank) :
    ambientTensorWeight (ambientContractInvariant T C)
      =
    ambientTensorWeight T := by
  simp only [ambientTensorWeight, ambientContractInvariant]
  rw [Nat.cast_sub hC]
  push_cast
  ring

namespace ScalarInvariant

/-- Rational scalar multiplication. -/
def qsmul (c : Rat) (I : ScalarInvariant) : ScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.scalarMul c I.1.expr
      rank := 0
      weight := I.1.weight
      parity := I.1.parity
    },
    rfl
  ⟩

/-- Sum of homogeneous scalar invariants of the same weight. -/
def add
    (I J : ScalarInvariant)
    (_hWeight : I.1.weight = J.1.weight) :
    ScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.add I.1.expr J.1.expr
      rank := 0
      weight := I.1.weight
      parity := InvariantParity.mixed
    },
    rfl
  ⟩

/-- Base Laplacian, lowering weight by two. -/
def laplacian (I : ScalarInvariant) : ScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.laplacian I.1.expr
      rank := 0
      weight := I.1.weight - 2
      parity := I.1.parity
    },
    rfl
  ⟩

/-- Multiplication by the normalized scalar curvature `J`. -/
def jMul (I : ScalarInvariant) : ScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.jMul I.1.expr
      rank := 0
      weight := I.1.weight - 2
      parity := I.1.parity
    },
    rfl
  ⟩

end ScalarInvariant

/-- Divergence of a rank-one invariant. -/
def divInvariant (F : OneFormInvariant) : ScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.divergence F.1.expr
      rank := 0
      weight := F.1.weight - 2
      parity := F.1.parity
    },
    rfl
  ⟩

/-- Ambient divergence of a rank-one invariant. -/
def ambientDivInvariant
    (F : AmbientOneFormInvariant) :
    AmbientScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.divergence F.1.expr
      rank := 0
      weight := F.1.weight - 2
      parity := F.1.parity
    },
    rfl
  ⟩

namespace AmbientScalarInvariant

/-- Ambient Laplacian, lowering weight by two. -/
def laplacian (I : AmbientScalarInvariant) : AmbientScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.ambientLaplacian I.1.expr
      rank := 0
      weight := I.1.weight - 2
      parity := I.1.parity
    },
    rfl
  ⟩

end AmbientScalarInvariant

/--
Restriction of a scalar ambient invariant to the Einstein slice.

This is the `i^*` appearing in Theorem 1.4; it is not restriction to the
conformal boundary of the PE manifold.
-/
def restrictToEinsteinSlice
    (I : AmbientScalarInvariant) :
    ScalarInvariant :=
  ⟨
    {
      expr := TensorInvariantExpr.restrictAmbient I.1.expr
      rank := 0
      weight := I.1.weight
      parity := I.1.parity
    },
    rfl
  ⟩

end PE
end Ambient
end ConformalStructure
