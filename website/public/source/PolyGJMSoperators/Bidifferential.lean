import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.Tangential

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
# Rank-two specialization: bidifferential ambient operators
-/

/-- Rank-two inputs. -/
abbrev BiInput : Type _ :=
  CalConf.MultiInput 2

/-- Rank-two input weights. -/
def biWeights (_CalConf : Calculus Conf) (w₁ w₂ : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then w₁ else w₂

/-- Build a rank-two input from two ambient functions. -/
def pairInput (f g : Function Conf) :
    CalConf.BiInput :=
  fun i => if i = 0 then f else g

/-- The left input slot. -/
def leftInput (F : CalConf.BiInput) :
    Function Conf :=
  F 0

/-- The right input slot. -/
def rightInput (F : CalConf.BiInput) :
    Function Conf :=
  F 1

/-- Readable bidifferential tangentiality predicate. -/
def IsBiTangentialAtWeights
    (B : CalConf.BiOperator)
    (w₁ w₂ : ℝ) : Prop :=
  CalConf.IsTangentialAtWeights B (CalConf.biWeights w₁ w₂)

/-- Readable bidifferential homogeneity predicate. -/
def IsBiHomogeneous
    (w₁ w₂ : ℝ)
    (F : CalConf.BiInput) : Prop :=
  CalConf.IsMultiHomogeneous (CalConf.biWeights w₁ w₂) F

/-- Expected output weight for a bidifferential operator of total degree `N`. -/
def biOutputWeight
    (w₁ w₂ : ℝ)
    (N : ℕ) : ℝ :=
  CalConf.outputWeight (CalConf.biWeights w₁ w₂) N

@[simp]
theorem biWeights_zero
    (w₁ w₂ : ℝ) :
    CalConf.biWeights w₁ w₂ 0 = w₁ := by
  simp [biWeights]

@[simp]
theorem biWeights_one
    (w₁ w₂ : ℝ) :
    CalConf.biWeights w₁ w₂ 1 = w₂ := by
  norm_num [biWeights]

@[simp]
theorem pairInput_zero
    (f g : Function Conf) :
    CalConf.pairInput f g 0 = f := by
  simp [pairInput]

@[simp]
theorem pairInput_one
    (f g : Function Conf) :
    CalConf.pairInput f g 1 = g := by
  norm_num [pairInput]

@[simp]
theorem leftInput_pairInput
    (f g : Function Conf) :
    CalConf.leftInput (CalConf.pairInput f g) = f := by
  rfl

@[simp]
theorem rightInput_pairInput
    (f g : Function Conf) :
    CalConf.rightInput (CalConf.pairInput f g) = g := by
  rfl

theorem totalWeight_biWeights
    (w₁ w₂ : ℝ) :
    CalConf.totalWeight (CalConf.biWeights w₁ w₂) = w₁ + w₂ := by
  rw [CalConf.totalWeight_fin_two]
  simp

theorem biOutputWeight_eq
    (w₁ w₂ : ℝ)
    (N : ℕ) :
    CalConf.biOutputWeight w₁ w₂ N =
      w₁ + w₂ - 2 * (N : ℝ) := by
  unfold biOutputWeight outputWeight
  rw [CalConf.totalWeight_biWeights]

end Calculus
end Operators
end Ambient
end ConformalStructure
