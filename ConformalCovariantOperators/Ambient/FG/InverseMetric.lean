import ConformalCovariantOperators.Ambient.FG.NormalForm

open Classical
open scoped BigOperators

noncomputable section

universe w

namespace ConformalStructure
namespace Ambient
namespace FG

variable {ι : Type w}

/-!
# Inverse metric in normal form

The inverse metric has the block form

`g~^{00} = 0`, `g~^{0 inf} = t^{-1}`,
`g~^{ij} = t^{-2} g^{ij}`, and
`g~^{inf inf} = -2 rho t^{-2}`.

This file records the component formulas and proves the base-block inverse
calculation from the base inverse hypothesis.
-/

/-- Normal metric components together with a formal inverse base block. -/
structure NormalInverseMetricComponents (ι : Type w) extends NormalMetricComponents ι where
  /-- The inverse base block `g^{ij}`. -/
  gInv : ι → ι → ℝ

/-- The normal-form inverse ambient metric components `g~^IJ`. -/
def inverseMetricComp (C : NormalInverseMetricComponents ι) :
    AmbientIndex ι → AmbientIndex ι → ℝ
  | AmbientIndex.zero, AmbientIndex.zero => 0
  | AmbientIndex.zero, AmbientIndex.base _ => 0
  | AmbientIndex.zero, AmbientIndex.inf => C.t⁻¹
  | AmbientIndex.base _, AmbientIndex.zero => 0
  | AmbientIndex.base i, AmbientIndex.base j => (C.t ^ 2)⁻¹ * C.gInv i j
  | AmbientIndex.base _, AmbientIndex.inf => 0
  | AmbientIndex.inf, AmbientIndex.zero => C.t⁻¹
  | AmbientIndex.inf, AmbientIndex.base _ => 0
  | AmbientIndex.inf, AmbientIndex.inf => -2 * C.rho * (C.t ^ 2)⁻¹

@[simp]
theorem inverseMetricComp_zero_zero (C : NormalInverseMetricComponents ι) :
    inverseMetricComp C AmbientIndex.zero AmbientIndex.zero = 0 := rfl

@[simp]
theorem inverseMetricComp_zero_inf (C : NormalInverseMetricComponents ι) :
    inverseMetricComp C AmbientIndex.zero AmbientIndex.inf = C.t⁻¹ := rfl

@[simp]
theorem inverseMetricComp_inf_zero (C : NormalInverseMetricComponents ι) :
    inverseMetricComp C AmbientIndex.inf AmbientIndex.zero = C.t⁻¹ := rfl

@[simp]
theorem inverseMetricComp_base_base
    (C : NormalInverseMetricComponents ι) (i j : ι) :
    inverseMetricComp C (AmbientIndex.base i) (AmbientIndex.base j)
      = (C.t ^ 2)⁻¹ * C.gInv i j := rfl

@[simp]
theorem inverseMetricComp_inf_inf (C : NormalInverseMetricComponents ι) :
    inverseMetricComp C AmbientIndex.inf AmbientIndex.inf
      = -2 * C.rho * (C.t ^ 2)⁻¹ := rfl

/-- Left inverse condition for the base block. -/
def BaseLeftInverse
    [Fintype ι] [DecidableEq ι]
    (C : NormalInverseMetricComponents ι) : Prop :=
  ∀ i j : ι, (∑ k : ι, C.gInv i k * C.g k j) = if i = j then 1 else 0

/-- Right inverse condition for the base block. -/
def BaseRightInverse
    [Fintype ι] [DecidableEq ι]
    (C : NormalInverseMetricComponents ι) : Prop :=
  ∀ i j : ι, (∑ k : ι, C.g i k * C.gInv k j) = if i = j then 1 else 0

/--
The base-base block of `g~^{IK} g~_{KJ}` reduces to the ordinary inverse
identity for `g^{ik} g_kj`.
-/
theorem inverse_metric_base_base_left
    [Fintype ι] [DecidableEq ι]
    (C : NormalInverseMetricComponents ι)
    (ht : C.t ≠ 0)
    (hbase : BaseLeftInverse C)
    (i j : ι) :
    (∑ k : ι,
        inverseMetricComp C (AmbientIndex.base i) (AmbientIndex.base k)
          * ambientMetricComp C.toNormalMetricComponents
              (AmbientIndex.base k) (AmbientIndex.base j))
      =
    AmbientIndex.kronecker (AmbientIndex.base i) (AmbientIndex.base j) := by
  classical
  calc
    (∑ k : ι,
        inverseMetricComp C (AmbientIndex.base i) (AmbientIndex.base k)
          * ambientMetricComp C.toNormalMetricComponents
              (AmbientIndex.base k) (AmbientIndex.base j))
        = ∑ k : ι, C.gInv i k * C.g k j := by
            apply Finset.sum_congr rfl
            intro k _hk
            simp [inverseMetricComp, ambientMetricComp]
            field_simp [pow_ne_zero 2 ht]
    _ = AmbientIndex.kronecker (AmbientIndex.base i) (AmbientIndex.base j) := by
            rw [hbase i j]
            by_cases hij : i = j
            · simp [AmbientIndex.kronecker, hij]
            · simp [AmbientIndex.kronecker, hij]

end FG
end Ambient
end ConformalStructure
