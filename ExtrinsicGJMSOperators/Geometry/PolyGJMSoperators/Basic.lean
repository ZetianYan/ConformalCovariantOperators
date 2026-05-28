import Mathlib
import ExtrinsicGJMSOperators.Geometry.Ambient.Ambienttangential

open Classical

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
# Basic rank-r ambient inputs and operators

This file defines the uniform rank-r input object used for unary,
bidifferential, tridifferential, and higher multilinear ambient operators.
-/

/-- A rank-r tuple of ambient functions. -/
abbrev MultiInput (_CalConf : Calculus Conf) (r : ℕ) : Type _ :=
  Fin r → Function Conf

/-- A rank-r ambient operator. -/
abbrev MultiOperator (CalConf : Calculus Conf) (r : ℕ) : Type _ :=
  CalConf.MultiInput r → Function Conf

/-- Rank-one multi-operators. -/
abbrev UnaryMultiOperator : Type _ :=
  CalConf.MultiOperator 1

/-- Rank-two multi-operators, i.e. bidifferential ambient operators. -/
abbrev BiOperator : Type _ :=
  CalConf.MultiOperator 2

/-- Rank-three multi-operators, i.e. tridifferential ambient operators. -/
abbrev TriOperator : Type _ :=
  CalConf.MultiOperator 3

/-- Regard an ordinary unary ambient operator as a rank-one multi-operator. -/
def unaryToMulti
    (P : Function Conf → Function Conf) :
    CalConf.MultiOperator 1 :=
  fun F => P (F 0)

/-- Regard a rank-one multi-operator as an ordinary unary ambient operator. -/
def multiToUnary
    (P : CalConf.MultiOperator 1) :
    Function Conf → Function Conf :=
  fun f => P (fun _ => f)

@[simp]
theorem unaryToMulti_apply
    (P : Function Conf → Function Conf)
    (F : CalConf.MultiInput 1) :
    CalConf.unaryToMulti P F = P (F 0) := by
  rfl

@[simp]
theorem multiToUnary_apply
    (P : CalConf.MultiOperator 1)
    (f : Function Conf) :
    CalConf.multiToUnary P f = P (fun _ => f) := by
  rfl

namespace MultiInput

variable {CalConf}

/-- Replace one input slot. -/
def replace
    {r : ℕ}
    (F : CalConf.MultiInput r)
    (i : Fin r)
    (f : Function Conf) :
    CalConf.MultiInput r :=
  Function.update F i f

/-- Apply the same unary operator to every input slot. -/
def mapUnary
    {r : ℕ}
    (P : Function Conf → Function Conf)
    (F : CalConf.MultiInput r) :
    CalConf.MultiInput r :=
  fun i => P (F i)

@[simp]
theorem replace_same
    {r : ℕ}
    (F : CalConf.MultiInput r)
    (i : Fin r)
    (f : Function Conf) :
    replace F i f i = f := by
  classical
  simp [replace]

@[simp]
theorem mapUnary_apply
    {r : ℕ}
    (P : Function Conf → Function Conf)
    (F : CalConf.MultiInput r)
    (i : Fin r) :
    mapUnary P F i = P (F i) := by
  rfl

end MultiInput

end Calculus
end Operators
end Ambient
end ConformalStructure
