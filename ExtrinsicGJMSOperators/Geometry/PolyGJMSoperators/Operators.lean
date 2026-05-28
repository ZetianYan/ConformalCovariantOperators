import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.Homogeneity

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
# Algebra of rank-r ambient operators
-/

/-- The zero rank-r multi-operator. -/
def multiZero (r : ℕ) :
    CalConf.MultiOperator r :=
  fun _ => zero Conf

/-- Pointwise sum of rank-r multi-operators. -/
def multiAdd
    {r : ℕ}
    (P Q : CalConf.MultiOperator r) :
    CalConf.MultiOperator r :=
  fun F U => P F U + Q F U

/-- Pointwise difference of rank-r multi-operators. -/
def multiSub
    {r : ℕ}
    (P Q : CalConf.MultiOperator r) :
    CalConf.MultiOperator r :=
  fun F U => P F U - Q F U

/-- Scalar multiple of a rank-r multi-operator. -/
def multiSmul
    {r : ℕ}
    (c : ℝ)
    (P : CalConf.MultiOperator r) :
    CalConf.MultiOperator r :=
  fun F U => c * P F U

/-- Apply a unary operator after a rank-r multi-operator. -/
def postcomp
    {r : ℕ}
    (L : Function Conf → Function Conf)
    (P : CalConf.MultiOperator r) :
    CalConf.MultiOperator r :=
  fun F => L (P F)

/-- Apply a unary operator to one input slot before a rank-r multi-operator. -/
def precompSlot
    {r : ℕ}
    (i : Fin r)
    (L : Function Conf → Function Conf)
    (P : CalConf.MultiOperator r) :
    CalConf.MultiOperator r :=
  fun F => P (MultiInput.replace F i (L (F i)))

/-- Apply slot-dependent unary operators before a rank-r multi-operator. -/
def precompAll
    {r : ℕ}
    (L : Fin r → Function Conf → Function Conf)
    (P : CalConf.MultiOperator r) :
    CalConf.MultiOperator r :=
  fun F => P (fun i => L i (F i))

@[simp]
theorem multiZero_apply
    {r : ℕ}
    (F : CalConf.MultiInput r) :
    CalConf.multiZero r F = zero Conf := by
  rfl

@[simp]
theorem multiAdd_apply
    {r : ℕ}
    (P Q : CalConf.MultiOperator r)
    (F : CalConf.MultiInput r)
    (U : Conf.AmbientBundle) :
    CalConf.multiAdd P Q F U = P F U + Q F U := by
  rfl

@[simp]
theorem multiSmul_apply
    {r : ℕ}
    (c : ℝ)
    (P : CalConf.MultiOperator r)
    (F : CalConf.MultiInput r)
    (U : Conf.AmbientBundle) :
    CalConf.multiSmul c P F U = c * P F U := by
  rfl

@[simp]
theorem postcomp_apply
    {r : ℕ}
    (L : Function Conf → Function Conf)
    (P : CalConf.MultiOperator r)
    (F : CalConf.MultiInput r) :
    CalConf.postcomp L P F = L (P F) := by
  rfl

end Calculus
end Operators
end Ambient
end ConformalStructure
