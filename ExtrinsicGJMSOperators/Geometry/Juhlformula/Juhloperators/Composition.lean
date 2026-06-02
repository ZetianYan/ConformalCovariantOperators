import Mathlib
import ExtrinsicGJMSOperators.Geometry.Juhlformula.Juhloperators.Basic
import ExtrinsicGJMSOperators.Geometry.GJMSoperators.Basic

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

/-- Ordinary composition of unary ambient operators. -/
def composeUnary
    (P Q : Function Conf → Function Conf) :
    Function Conf → Function Conf :=
  fun f => P (Q f)

@[simp]
theorem composeUnary_apply
    (P Q : Function Conf → Function Conf)
    (f : Function Conf) :
    composeUnary P Q f = P (Q f) := by
  rfl

/-- The identity unary operator. -/
def idUnary : Function Conf → Function Conf :=
  fun f => f

@[simp]
theorem idUnary_apply
    (f : Function Conf) :
    idUnary f = f := by
  rfl

/-- Extract the underlying ambient unary operator from an abstract GJMS operator. -/
def abstractToUnary
    (P : GJMS.AbstractOperator CalConf) :
    Function Conf → Function Conf :=
  P.toWeightedTangentialOperator.toOperator

@[simp]
theorem abstractToUnary_apply
    (P : GJMS.AbstractOperator CalConf)
    (f : Function Conf) :
    abstractToUnary CalConf P f =
      P.toWeightedTangentialOperator.toOperator f := by
  rfl

/-- Compose a list of unary operators from left to right.

For `[P_1, P_2, P_3]`, this gives `P_1 ∘ P_2 ∘ P_3`.
-/
def composeUnaryList :
    List (Function Conf → Function Conf) → Function Conf → Function Conf
  | [] => idUnary
  | P :: Ps => composeUnary P (composeUnaryList Ps)

@[simp]
theorem composeUnaryList_nil :
    composeUnaryList (Conf := Conf) [] = idUnary := by
  rfl

@[simp]
theorem composeUnaryList_cons
    (P : Function Conf → Function Conf)
    (Ps : List (Function Conf → Function Conf)) :
    composeUnaryList (Conf := Conf) (P :: Ps)
      =
    composeUnary P (composeUnaryList Ps) := by
  rfl

/-- A general abstract GJMS family indexed by positive integers. -/
abbrev AbstractGJMSFamily :=
  (k : Nat) → 0 < k → GJMS.AbstractOperator CalConf

/-- The list of underlying unary operators associated to a composition. -/
def operatorListOfComposition
    (G : AbstractGJMSFamily CalConf)
    {N : Nat}
    (I : Composition N) :
    List (Function Conf → Function Conf) :=
  I.parts.attach.map fun x =>
    abstractToUnary CalConf (G x.val (I.positive x.val x.property))

/-- The composed GJMS operator associated to `I`. -/
def composeGJMS
    (G : AbstractGJMSFamily CalConf)
    {N : Nat}
    (I : Composition N) :
    Function Conf → Function Conf :=
  composeUnaryList (operatorListOfComposition CalConf G I)

@[simp]
theorem operatorList_singleton
    (G : AbstractGJMSFamily CalConf)
    (N : Nat) (hN : 0 < N) :
    operatorListOfComposition CalConf G (Composition.singleton N hN)
      =
    [abstractToUnary CalConf (G N hN)] := by
  simp [operatorListOfComposition, Composition.singleton]

@[simp]
theorem composeGJMS_singleton
    (G : AbstractGJMSFamily CalConf)
    (N : Nat) (hN : 0 < N) :
    composeGJMS CalConf G (Composition.singleton N hN)
      =
    abstractToUnary CalConf (G N hN) := by
  funext f
  simp [composeGJMS, operatorListOfComposition, Composition.singleton,
    composeUnaryList, idUnary, composeUnary]

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
