import ConformalCovariantOperators.Ambient.Ambientbasic
import ConformalCovariantOperators.Ambient.FG.Index

open Classical
open scoped BigOperators

noncomputable section

universe u v w

namespace ConformalStructure
namespace Ambient
namespace FG

variable {M : Type u}
variable {Conf : ConformalStructure.{u, v} M}
variable {ι : Type w}

/-!
# Normal-form ambient metric data

This file keeps two levels separate.

* `NormalAmbientData` packages the existing straight metric data over a chosen
  conformal scale.
* `NormalMetricComponents` is the pointwise coordinate component model used for
  the first Fefferman-Graham calculations.

The component model records the straight normal form

`g~ = 2 rho dt^2 + 2 t dt d rho + t^2 g_ij(x,rho) dx^i dx^j`.
-/

/-- Fefferman-Graham normal ambient data extending the existing straight data. -/
structure NormalAmbientData (Conf : ConformalStructure.{u, v} M) where
  straightData : Conf.StraightMetricData

namespace NormalAmbientData

/-- The existing straight-form wrapper attached to normal ambient data. -/
def toStraightForm (A : NormalAmbientData Conf) : Conf.StraightForm where
  data := A.straightData

/-- The chosen base scale. -/
def baseScale (A : NormalAmbientData Conf) : Conf.Scale :=
  A.straightData.baseScale

/-- The one-parameter family `g_rho`. -/
def gRho (A : NormalAmbientData Conf) : ℝ → Conf.MetricField :=
  A.straightData.gRho

@[simp]
theorem compat0 (A : NormalAmbientData Conf) (x : M) :
    Conf.toFiber (A.gRho 0 x) = A.baseScale.metric x :=
  A.straightData.compat0 x

end NormalAmbientData

/-- Pointwise base metric components in a normal-form coordinate frame. -/
structure NormalMetricComponents (ι : Type w) where
  /-- The scale coordinate `t`. -/
  t : ℝ
  /-- The normal coordinate `rho`. -/
  rho : ℝ
  /-- The base block `g_ij(x,rho)`. -/
  g : ι → ι → ℝ

/-- The normal-form ambient metric components `g~_IJ`. -/
def ambientMetricComp (C : NormalMetricComponents ι) :
    AmbientIndex ι → AmbientIndex ι → ℝ
  | AmbientIndex.zero, AmbientIndex.zero => 2 * C.rho
  | AmbientIndex.zero, AmbientIndex.base _ => 0
  | AmbientIndex.zero, AmbientIndex.inf => C.t
  | AmbientIndex.base _, AmbientIndex.zero => 0
  | AmbientIndex.base i, AmbientIndex.base j => C.t ^ 2 * C.g i j
  | AmbientIndex.base _, AmbientIndex.inf => 0
  | AmbientIndex.inf, AmbientIndex.zero => C.t
  | AmbientIndex.inf, AmbientIndex.base _ => 0
  | AmbientIndex.inf, AmbientIndex.inf => 0

@[simp]
theorem ambientMetricComp_zero_zero (C : NormalMetricComponents ι) :
    ambientMetricComp C AmbientIndex.zero AmbientIndex.zero = 2 * C.rho := rfl

@[simp]
theorem ambientMetricComp_zero_base (C : NormalMetricComponents ι) (i : ι) :
    ambientMetricComp C AmbientIndex.zero (AmbientIndex.base i) = 0 := rfl

@[simp]
theorem ambientMetricComp_base_zero (C : NormalMetricComponents ι) (i : ι) :
    ambientMetricComp C (AmbientIndex.base i) AmbientIndex.zero = 0 := rfl

@[simp]
theorem ambientMetricComp_zero_inf (C : NormalMetricComponents ι) :
    ambientMetricComp C AmbientIndex.zero AmbientIndex.inf = C.t := rfl

@[simp]
theorem ambientMetricComp_inf_zero (C : NormalMetricComponents ι) :
    ambientMetricComp C AmbientIndex.inf AmbientIndex.zero = C.t := rfl

@[simp]
theorem ambientMetricComp_base_base (C : NormalMetricComponents ι) (i j : ι) :
    ambientMetricComp C (AmbientIndex.base i) (AmbientIndex.base j)
      = C.t ^ 2 * C.g i j := rfl

@[simp]
theorem ambientMetricComp_base_inf (C : NormalMetricComponents ι) (i : ι) :
    ambientMetricComp C (AmbientIndex.base i) AmbientIndex.inf = 0 := rfl

@[simp]
theorem ambientMetricComp_inf_base (C : NormalMetricComponents ι) (i : ι) :
    ambientMetricComp C AmbientIndex.inf (AmbientIndex.base i) = 0 := rfl

@[simp]
theorem ambientMetricComp_inf_inf (C : NormalMetricComponents ι) :
    ambientMetricComp C AmbientIndex.inf AmbientIndex.inf = 0 := rfl

/-- Symmetry of the ambient metric follows from symmetry of the base block. -/
theorem ambientMetricComp_symm
    (C : NormalMetricComponents ι)
    (hg : ∀ i j : ι, C.g i j = C.g j i)
    (I J : AmbientIndex ι) :
    ambientMetricComp C I J = ambientMetricComp C J I := by
  cases I <;> cases J <;> simp [ambientMetricComp, hg]

end FG
end Ambient
end ConformalStructure
