import ConformalCovariantOperators.Ambient.FG.InverseMetric

open Classical
open scoped BigOperators

noncomputable section

universe w

namespace ConformalStructure
namespace Ambient
namespace FG

variable {ι : Type w}

/-!
# Christoffel symbols in normal form

This file records the first raised-index Christoffel formulas needed by the
ambient Laplacian and commutator calculations.  The remaining base-only
Christoffel symbols are kept as formal base data.
-/

/-- Component data needed for normal-form Christoffel symbols. -/
structure ChristoffelComponents (ι : Type w) extends NormalInverseMetricComponents ι where
  /-- `rho` derivative of the base metric block. -/
  dRhoG : ι → ι → ℝ
  /-- Christoffel symbols of the base metric `g_rho`. -/
  baseGamma : ι → ι → ι → ℝ

/-- Kronecker delta on base indices. -/
def baseDelta [DecidableEq ι] (i j : ι) : ℝ :=
  if i = j then 1 else 0

@[simp]
theorem baseDelta_self [DecidableEq ι] (i : ι) :
    baseDelta i i = 1 := by
  simp [baseDelta]

/-- Raised-index Christoffel symbols in straight normal form. -/
def christoffelComp [DecidableEq ι] (C : ChristoffelComponents ι) :
    AmbientIndex ι → AmbientIndex ι → AmbientIndex ι → ℝ
  | AmbientIndex.zero, AmbientIndex.base i, AmbientIndex.base j =>
      -(1 / 2 : ℝ) * C.t * C.dRhoG i j
  | AmbientIndex.base k, AmbientIndex.zero, AmbientIndex.base j =>
      C.t⁻¹ * baseDelta j k
  | AmbientIndex.base k, AmbientIndex.base j, AmbientIndex.zero =>
      C.t⁻¹ * baseDelta j k
  | AmbientIndex.inf, AmbientIndex.base i, AmbientIndex.base j =>
      -C.g i j + C.rho * C.dRhoG i j
  | AmbientIndex.base k, AmbientIndex.base i, AmbientIndex.base j =>
      C.baseGamma k i j
  | _, _, _ => 0

@[simp]
theorem christoffel_zero_base_base
    [DecidableEq ι] (C : ChristoffelComponents ι) (i j : ι) :
    christoffelComp C AmbientIndex.zero (AmbientIndex.base i) (AmbientIndex.base j)
      = -(1 / 2 : ℝ) * C.t * C.dRhoG i j := rfl

@[simp]
theorem christoffel_base_zero_base
    [DecidableEq ι] (C : ChristoffelComponents ι) (k j : ι) :
    christoffelComp C (AmbientIndex.base k) AmbientIndex.zero (AmbientIndex.base j)
      = C.t⁻¹ * baseDelta j k := rfl

@[simp]
theorem christoffel_base_base_zero
    [DecidableEq ι] (C : ChristoffelComponents ι) (k j : ι) :
    christoffelComp C (AmbientIndex.base k) (AmbientIndex.base j) AmbientIndex.zero
      = C.t⁻¹ * baseDelta j k := rfl

@[simp]
theorem christoffel_inf_base_base
    [DecidableEq ι] (C : ChristoffelComponents ι) (i j : ι) :
    christoffelComp C AmbientIndex.inf (AmbientIndex.base i) (AmbientIndex.base j)
      = -C.g i j + C.rho * C.dRhoG i j := rfl

@[simp]
theorem christoffel_base_base_base
    [DecidableEq ι] (C : ChristoffelComponents ι) (k i j : ι) :
    christoffelComp C (AmbientIndex.base k) (AmbientIndex.base i) (AmbientIndex.base j)
      = C.baseGamma k i j := rfl

end FG
end Ambient
end ConformalStructure
