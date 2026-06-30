import Mathlib
import ConformalCovariantOperators.GJMSoperators.Basic

open Classical

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace GJMS

variable {M : Type u}
variable {Conf : ConformalStructure.{u, v} M}
variable (CalConf : Calculus Conf)

/-!
# Ambient construction of GJMS-type operators

This file packages powers of the formal ambient Laplacian as GJMS-type
operators.

The actual tangentiality theorem

`Δ̃^k is tangential at weight k - n / 2`

is not proved here. Instead, this file assumes that tangentiality has already
been proved and then constructs the corresponding abstract GJMS operator.

The dependency structure is:

* `Ambient.Tangential` defines weighted tangential operators;
* `GJMS.Basic` defines abstract GJMS operators;
* this file constructs the GJMS operator from `Δ̃^k`, assuming tangentiality.
-/


/-! ## Ambient Laplacian powers as operators -/

/--
The ambient Laplacian power operator `Δ̃^k`.

At this formal level, this is just the operator

`f ↦ lapPow k f`.
-/
def ambientLaplacianPowerOperator (k : ℕ) :
    Operator (Conf := Conf) :=
  fun f => CalConf.lapPow k f

@[simp]
theorem ambientLaplacianPowerOperator_apply
    (k : ℕ) (f : Function Conf) :
    ambientLaplacianPowerOperator CalConf k f =
      CalConf.lapPow k f := by
  rfl

@[simp]
theorem ambientLaplacianPowerOperator_zero_apply
    (f : Function Conf) :
    ambientLaplacianPowerOperator CalConf 0 f = f := by
  unfold ambientLaplacianPowerOperator
  simp [lapPow]

@[simp]
theorem ambientLaplacianPowerOperator_one_apply
    (f : Function Conf) :
    ambientLaplacianPowerOperator CalConf 1 f = CalConf.lap f := by
  unfold ambientLaplacianPowerOperator
  simp [lapPow]


/-! ## Weight bookkeeping for ambient Laplacian powers -/

/--
The operator `Δ̃^k` maps the GJMS input weight to the GJMS output weight.

This is the weight bookkeeping theorem. It uses the already established
homogeneity theorem for `lapPow`.
-/
theorem ambientLaplacianPower_maps_GJMS_weight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    CalConf.MapsHomogeneousWeight
      (ambientLaplacianPowerOperator CalConf k)
      (calculusInputWeight CalConf k)
      (calculusOutputWeight CalConf k) := by
  intro f hf
  unfold ambientLaplacianPowerOperator
  have h := CalConf.lapPow_isXHomogeneous H k hf
  unfold LapPowHasWeight at h
  convert h using 1
  unfold calculusInputWeight calculusOutputWeight
  unfold inputWeight outputWeight
  ring

/--
A slightly more explicit version of the previous theorem.
-/
theorem lapPow_maps_GJMS_weight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    {f : Function Conf}
    (hf : CalConf.IsXHomogeneous (calculusInputWeight CalConf k) f) :
    CalConf.IsXHomogeneous
      (calculusOutputWeight CalConf k)
      (CalConf.lapPow k f) := by
  exact ambientLaplacianPower_maps_GJMS_weight CalConf H k hf


/-! ## Weighted tangential operator from ambient Laplacian powers -/

/--
If `Δ̃^k` is tangential at the GJMS input weight, then it defines a weighted
tangential operator

`E[k - n / 2] → E[-k - n / 2]`.
-/
def ambientLaplacianPowerWeightedTangentialOperator
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (htangential :
      CalConf.IsTangentialAtWeight
        (ambientLaplacianPowerOperator CalConf k)
        (calculusInputWeight CalConf k)) :
    CalConf.WeightedTangentialOperator where
  inputWeight := calculusInputWeight CalConf k
  outputWeight := calculusOutputWeight CalConf k
  toOperator := ambientLaplacianPowerOperator CalConf k
  mapsWeight := ambientLaplacianPower_maps_GJMS_weight CalConf H k
  tangential := htangential

@[simp]
theorem ambientLaplacianPowerWeightedTangentialOperator_inputWeight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (htangential :
      CalConf.IsTangentialAtWeight
        (ambientLaplacianPowerOperator CalConf k)
        (calculusInputWeight CalConf k)) :
    (ambientLaplacianPowerWeightedTangentialOperator CalConf H k htangential).inputWeight
      =
    calculusInputWeight CalConf k := by
  rfl

@[simp]
theorem ambientLaplacianPowerWeightedTangentialOperator_outputWeight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (htangential :
      CalConf.IsTangentialAtWeight
        (ambientLaplacianPowerOperator CalConf k)
        (calculusInputWeight CalConf k)) :
    (ambientLaplacianPowerWeightedTangentialOperator CalConf H k htangential).outputWeight
      =
    calculusOutputWeight CalConf k := by
  rfl

@[simp]
theorem ambientLaplacianPowerWeightedTangentialOperator_toOperator
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (htangential :
      CalConf.IsTangentialAtWeight
        (ambientLaplacianPowerOperator CalConf k)
        (calculusInputWeight CalConf k)) :
    (ambientLaplacianPowerWeightedTangentialOperator CalConf H k htangential).toOperator
      =
    ambientLaplacianPowerOperator CalConf k := by
  rfl


/-! ## Abstract GJMS operator from ambient powers -/

/--
Assuming the ambient Laplacian power is tangential at the GJMS input weight,
package it as an abstract GJMS operator.
-/
def ambientLaplacianPowerAbstractOperator
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (htangential :
      CalConf.IsTangentialAtWeight
        (ambientLaplacianPowerOperator CalConf k)
        (calculusInputWeight CalConf k)) :
    AbstractOperator CalConf where
  k := k
  toWeightedTangentialOperator :=
    ambientLaplacianPowerWeightedTangentialOperator CalConf H k htangential
  inputWeight_eq := rfl
  outputWeight_eq := rfl

@[simp]
theorem ambientLaplacianPowerAbstractOperator_k
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (htangential :
      CalConf.IsTangentialAtWeight
        (ambientLaplacianPowerOperator CalConf k)
        (calculusInputWeight CalConf k)) :
    (ambientLaplacianPowerAbstractOperator CalConf H k htangential).k = k := by
  rfl

@[simp]
theorem ambientLaplacianPowerAbstractOperator_order
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (htangential :
      CalConf.IsTangentialAtWeight
        (ambientLaplacianPowerOperator CalConf k)
        (calculusInputWeight CalConf k)) :
    (ambientLaplacianPowerAbstractOperator CalConf H k htangential).order = 2 * k := by
  rfl

end GJMS
end Calculus
end Operators
end Ambient
end ConformalStructure
