import Mathlib
import ExtrinsicGJMSOperators.Geometry.GJMSoperators.Ambientconstruction

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
# Tangentiality of ambient Laplacian powers

This file isolates the algebraic core needed to prove that the ambient
Laplacian powers descend to the boundary.

The main mathematical statement is:

If `f₁` and `f₂` are homogeneous ambient extensions of the same boundary
density, then

`Δ̃^k f₁` and `Δ̃^k f₂`

also have the same boundary value, provided the input weight is the critical
GJMS weight

`k - n / 2`.

Equivalently, the operator `Δ̃^k` is tangential at weight `k - n / 2`.

The required linearity and commutator formulas are proved in
`Ambientoperator.lean`; weighted boundary equivalence records the homogeneous
`Q`-error directly, avoiding any global cancellation of `Q`.
-/


/-! ## Local helper lemmas -/

/--
Every `Q`-multiple vanishes modulo `Q`.

This duplicate local lemma keeps this file independent of theorem names in
`Tangential.lean`.
-/
theorem vanishesModQ_Qmul_local
    (h : Function Conf) :
    CalConf.VanishesModQ (CalConf.Qmul h) := by
  unfold VanishesModQ
  exact ⟨h, rfl⟩

/--
A local way to construct equality modulo `Q`.
-/
theorem sameBoundaryValue_of_difference_vanishes
    {f g : Function Conf}
    (h : CalConf.VanishesModQ (fun U => f U - g U)) :
    CalConf.SameBoundaryValue f g := by
  unfold SameBoundaryValue EqModQ
  exact h


/-! ## Critical `Q`-errors -/

/--
The key vanishing statement:

If `h` has the critical error weight

`k - n / 2 - 2`,

then

`Δ̃^k(Qh)` vanishes modulo `Q`.

This is the precise algebraic reason why `Δ̃^k` descends to the boundary.
-/
theorem lapPow_Qmul_vanishes_at_criticalWeight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    {h : Function Conf}
    (hh :
      CalConf.IsXHomogeneous
        (calculusInputWeight CalConf k - 2)
        h) :
    CalConf.VanishesModQ
      (CalConf.lapPow k (CalConf.Qmul h)) := by
  cases k with
  | zero =>
      simpa [lapPow] using vanishesModQ_Qmul_local CalConf h

  | succ r =>
      unfold VanishesModQ
      refine ⟨CalConf.lapPow (r + 1) h, ?_⟩

      have hformula :=
        CalConf.lapPow_Qmul_formula H (r + 1) hh

      rw [hformula]
      funext U

      unfold Qmul
      unfold calculusInputWeight inputWeight

      have hcoeff :
          2 * ((r + 1 : ℕ) : ℝ)
              *
            (2 * (((r + 1 : ℕ) : ℝ) - CalConf.n / 2 - 2)
                + CalConf.n + 2 - 2 * ((r : ℕ) : ℝ))
            =
          0 := by
        rw [Nat.cast_add, Nat.cast_one]
        ring

      calc
        CalConf.Q U * CalConf.lapPow (r + 1) h U
            +
          2 * ((r + 1 : ℕ) : ℝ)
            *
          (2 * (((r + 1 : ℕ) : ℝ) - CalConf.n / 2 - 2)
            + CalConf.n + 2 - 2 * ((r : ℕ) : ℝ))
            *
          CalConf.lapPow r h U
            =
          CalConf.Q U * CalConf.lapPow (r + 1) h U := by
            rw [hcoeff]
            ring
        _ =
          CalConf.Q U * CalConf.lapPow (r + 1) h U := rfl


/--
If two homogeneous functions of the GJMS input weight differ by a `Q`-multiple,
then applying `Δ̃^k` preserves equality modulo `Q`.

This is the direct `mod Q` form of tangentiality.
-/
theorem lapPow_preserves_sameBoundaryValue_at_criticalWeight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    {f g : Function Conf}
    (_hf :
      CalConf.IsXHomogeneous
        (calculusInputWeight CalConf k)
        f)
    (_hg :
      CalConf.IsXHomogeneous
        (calculusInputWeight CalConf k)
        g)
    (hfg :
      CalConf.SameBoundaryValueAtWeight
        (calculusInputWeight CalConf k)
        f g) :
    CalConf.SameBoundaryValue
      (CalConf.lapPow k f)
      (CalConf.lapPow k g) := by
  unfold SameBoundaryValueAtWeight at hfg
  unfold SameBoundaryValue EqModQ VanishesModQ

  rcases hfg with ⟨h, hdiff, hh⟩

  have hvanish :
      CalConf.VanishesModQ
        (CalConf.lapPow k (CalConf.Qmul h)) :=
    lapPow_Qmul_vanishes_at_criticalWeight CalConf H k hh

  rcases hvanish with ⟨a, ha⟩
  refine ⟨a, ?_⟩

  have hsub :
      (fun U =>
          CalConf.lapPow k f U - CalConf.lapPow k g U)
        =
      CalConf.lapPow k (fun U => f U - g U) := by
    rw [CalConf.lapPow_sub H k f g]

  have hreplace :
      CalConf.lapPow k (fun U => f U - g U)
        =
      CalConf.lapPow k (CalConf.Qmul h) := by
    rw [hdiff]

  calc
    (fun U =>
        CalConf.lapPow k f U - CalConf.lapPow k g U)
        =
      CalConf.lapPow k (fun U => f U - g U) := hsub
    _ =
      CalConf.lapPow k (CalConf.Qmul h) := hreplace
    _ =
      CalConf.Qmul a := ha

/-! ## Main tangentiality theorem -/

/--
Main theorem: `Δ̃^k` is tangential at the GJMS critical input weight.

In other words,

`Δ̃^k : E[k - n / 2] → E[-k - n / 2]`

is well-defined on boundary densities, provided the extra tangentiality
identities are available.
-/
theorem lapPow_isTangentialAtCriticalWeight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    CalConf.IsTangentialAtWeight
      (ambientLaplacianPowerOperator CalConf k)
      (calculusInputWeight CalConf k) := by
  intro f g hf hg hfg
  unfold ambientLaplacianPowerOperator
  exact
    lapPow_preserves_sameBoundaryValue_at_criticalWeight CalConf H k hf hg hfg


/-! ## Canonical ambient GJMS operator from tangentiality identities -/

/--
The canonical ambient GJMS operator obtained from `Δ̃^k`, once the
tangentiality identities are available.
-/
def canonicalAmbientGJMS
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    AbstractOperator CalConf :=
  ambientLaplacianPowerAbstractOperator CalConf H k
    (lapPow_isTangentialAtCriticalWeight CalConf H k)

@[simp]
theorem canonicalAmbientGJMS_k
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    (canonicalAmbientGJMS CalConf H k).k = k := by
  unfold canonicalAmbientGJMS
  rfl

@[simp]
theorem canonicalAmbientGJMS_order
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    (canonicalAmbientGJMS CalConf H k).order = 2 * k := by
  unfold canonicalAmbientGJMS
  rfl

@[simp]
theorem canonicalAmbientGJMS_toOperator
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    (canonicalAmbientGJMS CalConf H k).toOperator =
      ambientLaplacianPowerOperator CalConf k := by
  unfold canonicalAmbientGJMS
  rfl

/--
Applying the canonical ambient GJMS operator is the same as applying
`lapPow k`.
-/
@[simp]
theorem canonicalAmbientGJMS_toOperator_apply
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (f : Function Conf) :
    (canonicalAmbientGJMS CalConf H k).toOperator f =
      CalConf.lapPow k f := by
  unfold canonicalAmbientGJMS
  rfl

/--
The canonical ambient GJMS operator maps the GJMS input weight to the GJMS
output weight.
-/
theorem canonicalAmbientGJMS_mapsWeight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    CalConf.MapsHomogeneousWeight
      (canonicalAmbientGJMS CalConf H k).toOperator
      (calculusInputWeight CalConf k)
      (calculusOutputWeight CalConf k) := by
  unfold canonicalAmbientGJMS
  exact
    (ambientLaplacianPowerWeightedTangentialOperator CalConf H k
      (lapPow_isTangentialAtCriticalWeight CalConf H k)).mapsWeight

/--
The canonical ambient GJMS operator is tangential at the GJMS input weight.
-/
theorem canonicalAmbientGJMS_tangential
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    CalConf.IsTangentialAtWeight
      (canonicalAmbientGJMS CalConf H k).toOperator
      (calculusInputWeight CalConf k) := by
  unfold canonicalAmbientGJMS
  exact
    (ambientLaplacianPowerWeightedTangentialOperator CalConf H k
      (lapPow_isTangentialAtCriticalWeight CalConf H k)).tangential


/-! ## Canonical GJMS family -/

/--
The whole canonical GJMS family obtained from all powers of the ambient
Laplacian.
-/
def canonicalAmbientGJMSFamily
    (H : CalConf.AlgebraicIdentities) :
    Family CalConf where
  operator := fun k => canonicalAmbientGJMS CalConf H k
  operator_k := by
    intro k
    rfl

@[simp]
theorem canonicalAmbientGJMSFamily_get
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    (canonicalAmbientGJMSFamily CalConf H).get k =
      canonicalAmbientGJMS CalConf H k := by
  rfl

@[simp]
theorem canonicalAmbientGJMSFamily_get_order
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    ((canonicalAmbientGJMSFamily CalConf H).get k).order = 2 * k := by
  rfl


/-! ## Low-order canonical operators -/

/--
The zeroth canonical ambient GJMS operator is represented by the identity.
-/
theorem canonicalAmbientGJMS_zero_toOperator_apply
    (H : CalConf.AlgebraicIdentities)
    (f : Function Conf) :
    (canonicalAmbientGJMS CalConf H 0).toOperator f = f := by
  simp [canonicalAmbientGJMS_toOperator_apply, lapPow]

/--
The first nontrivial canonical ambient GJMS operator is represented by the
ambient Laplacian.
-/
theorem canonicalAmbientGJMS_one_toOperator_apply
    (H : CalConf.AlgebraicIdentities)
    (f : Function Conf) :
    (canonicalAmbientGJMS CalConf H 1).toOperator f =
      CalConf.lap f := by
  simp [canonicalAmbientGJMS_toOperator_apply, lapPow]

/--
The second nontrivial canonical ambient GJMS operator is represented by
`lapPow 2`.
-/
theorem canonicalAmbientGJMS_two_toOperator_apply
    (H : CalConf.AlgebraicIdentities)
    (f : Function Conf) :
    (canonicalAmbientGJMS CalConf H 2).toOperator f =
      CalConf.lapPow 2 f := by
  simp [canonicalAmbientGJMS_toOperator_apply]


end GJMS
end Calculus
end Operators
end Ambient
end ConformalStructure
