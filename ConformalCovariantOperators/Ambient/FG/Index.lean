import Mathlib

open Classical
open scoped BigOperators

noncomputable section

universe u

namespace ConformalStructure
namespace Ambient
namespace FG

/-!
# Fefferman-Graham normal-form indices

This file introduces the three kinds of indices used in normal-form ambient
coordinates:

* `zero` for the scale coordinate `t`;
* `base i` for tangent indices on the base manifold;
* `inf` for the normal coordinate `rho`.

The base index type is intentionally abstract.  Later files can instantiate it
with finite coordinate charts, frame indices, or purely formal symbols.
-/

/-- Ambient normal-form indices: `0`, base indices, and `infinity`. -/
inductive AmbientIndex (ι : Type u) : Type u where
  | zero : AmbientIndex ι
  | base : ι → AmbientIndex ι
  | inf : AmbientIndex ι
deriving Repr, DecidableEq

namespace AmbientIndex

variable {ι : Type u}

/-- The Kronecker delta on ambient normal-form indices. -/
def kronecker [DecidableEq ι] (I J : AmbientIndex ι) : ℝ :=
  if I = J then 1 else 0

@[simp]
theorem kronecker_self [DecidableEq ι] (I : AmbientIndex ι) :
    kronecker I I = 1 := by
  simp [kronecker]

@[simp]
theorem kronecker_zero_inf [DecidableEq ι] :
    kronecker (ι := ι) zero inf = 0 := by
  simp [kronecker]

@[simp]
theorem kronecker_inf_zero [DecidableEq ι] :
    kronecker (ι := ι) inf zero = 0 := by
  simp [kronecker]

@[simp]
theorem kronecker_zero_base [DecidableEq ι] (i : ι) :
    kronecker zero (base i) = 0 := by
  simp [kronecker]

@[simp]
theorem kronecker_base_zero [DecidableEq ι] (i : ι) :
    kronecker (base i) zero = 0 := by
  simp [kronecker]

end AmbientIndex

/-- A chosen-scale normal-form coordinate triple `(t, x, rho)`. -/
structure NormalCoord (M : Type u) where
  t : ℝ
  x : M
  rho : ℝ

end FG
end Ambient
end ConformalStructure
