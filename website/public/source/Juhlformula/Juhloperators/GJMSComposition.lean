import Mathlib
import ConformalCovariantOperators.Juhlformula.Juhloperators.Composition
import ConformalCovariantOperators.GJMSoperators.Tangentiality

open Classical
open scoped BigOperators

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace Juhl

variable {M : Type u}
variable {Conf : ConformalStructure.{u, v} M}
variable (CalConf : Calculus Conf)

/-- The canonical GJMS family, viewed as a Juhl abstract family. -/
def canonicalJuhlGJMSFamily
    (H : CalConf.AlgebraicIdentities) :
    AbstractGJMSFamily CalConf :=
  fun k _hk => GJMS.canonicalAmbientGJMS CalConf H k

/-- The canonical GJMS composition associated to a composition `I`.

Mathematically: `P_{2I} = P_{2I_1} ∘ ... ∘ P_{2I_r}`.
-/
def canonicalGJMSComposition
    (H : CalConf.AlgebraicIdentities)
    {N : Nat}
    (I : Composition N) :
    Function Conf → Function Conf :=
  composeGJMS CalConf (canonicalJuhlGJMSFamily CalConf H) I

@[simp]
theorem canonicalGJMSComposition_singleton
    (H : CalConf.AlgebraicIdentities)
    (N : Nat) (hN : 0 < N) :
    canonicalGJMSComposition CalConf H (Composition.singleton N hN)
      =
    abstractToUnary CalConf (GJMS.canonicalAmbientGJMS CalConf H N) := by
  simp [canonicalGJMSComposition, canonicalJuhlGJMSFamily]

@[simp]
theorem canonicalGJMSComposition_singleton_apply
    (H : CalConf.AlgebraicIdentities)
    (N : Nat) (hN : 0 < N)
    (f : Function Conf) :
    canonicalGJMSComposition CalConf H (Composition.singleton N hN) f
      =
    (GJMS.canonicalAmbientGJMS CalConf H N).toWeightedTangentialOperator.toOperator f := by
  rw [canonicalGJMSComposition_singleton]
  rfl

@[simp]
theorem canonicalGJMSComposition_singleton_apply_lapPow
    (H : CalConf.AlgebraicIdentities)
    (N : Nat) (hN : 0 < N)
    (f : Function Conf) :
    canonicalGJMSComposition CalConf H (Composition.singleton N hN) f
      =
    CalConf.lapPow N f := by
  rw [canonicalGJMSComposition_singleton]
  change (GJMS.canonicalAmbientGJMS CalConf H N).toOperator f =
    CalConf.lapPow N f
  simp

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
