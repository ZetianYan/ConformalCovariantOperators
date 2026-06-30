import ConformalCovariantOperators.Ambient.FG.Recursion

open Classical
open scoped BigOperators

noncomputable section

universe w

namespace ConformalStructure
namespace Ambient
namespace FG

variable {ι : Type w}

/-!
# Even-dimensional obstruction scaffold

The Fefferman-Graham obstruction tensor appears at the critical even order.
This file introduces the finite-order data object that later calculations will
populate from the Ricci recursion.  It deliberately does not include
self-adjointness material.
-/

/-- The critical obstruction order `n / 2` in even dimension. -/
def obstructionOrder (n : ℕ) : ℕ :=
  n / 2

/-- A component-level obstruction tensor attached to a finite FG metric jet. -/
structure AmbientObstructionData
    (J : FormalMetricJet ι K) where
  /-- The base dimension. -/
  n : ℕ
  /-- We are in even dimension. -/
  even_dim : n % 2 = 0
  /-- The obstruction order is available in the finite jet. -/
  order_le : obstructionOrder n ≤ K
  /-- The obstruction tensor components. -/
  tensor : Sym2Component ι
  /-- Symmetry of the obstruction tensor. -/
  symmetric : SymmetricComponent tensor
  /-- Vanishing obstruction means the formal recursion can continue through the
  critical order in the eventual existence theorem. -/
  vanishing : Prop

namespace AmbientObstructionData

/-- The obstruction tensor as a component-level two-tensor. -/
def obstructionTensor
    (O : AmbientObstructionData (ι := ι) J) : Sym2Component ι :=
  O.tensor

theorem obstructionTensor_symmetric
    (O : AmbientObstructionData (ι := ι) J) :
    SymmetricComponent O.obstructionTensor :=
  O.symmetric

/-- A finite jet is formally unobstructed when its obstruction data vanishes. -/
def IsUnobstructed
    (O : AmbientObstructionData (ι := ι) J) : Prop :=
  O.vanishing

end AmbientObstructionData

end FG
end Ambient
end ConformalStructure
