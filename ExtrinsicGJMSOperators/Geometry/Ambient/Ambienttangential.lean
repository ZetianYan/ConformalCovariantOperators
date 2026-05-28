import Mathlib
import ExtrinsicGJMSOperators.Geometry.Ambient.Ambientoperator

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
# Tangential ambient operators

This file develops the formal `mod Q` framework for tangential ambient
operators.

The basic idea is:

* two ambient extensions have the same boundary value if they differ by a
  multiple of `Q`;
* an ambient operator is tangential if it preserves this equivalence relation;
* a weighted tangential operator is one which is tangential only on homogeneous
  functions of a fixed input weight.

This is the formal framework needed later to show that powers of the ambient
Laplacian induce GJMS-type boundary operators.
-/


/-! ## Boundary equivalence modulo `Q` -/

/--
Two ambient functions have the same boundary value if their difference is
divisible by `Q`.

This is a semantic alias for `EqModQ`.
-/
def SameBoundaryValue (f g : Function Conf) : Prop :=
  CalConf.EqModQ f g

/--
Weighted boundary equivalence for homogeneous ambient extensions.

Besides asking that `f - g` be a `Q`-multiple, this records that the error term
has the expected shifted homogeneity. This avoids any global cancellation or
division by `Q`.
-/
def SameBoundaryValueAtWeight
    (w : ℝ) (f g : Function Conf) : Prop :=
  ∃ h : Function Conf,
    (fun U => f U - g U) = CalConf.Qmul h
      ∧ CalConf.IsXHomogeneous (w - 2) h

theorem SameBoundaryValue_def (f g : Function Conf) :
    CalConf.SameBoundaryValue f g ↔ CalConf.EqModQ f g := by
  rfl

theorem SameBoundaryValueAtWeight.sameBoundaryValue
    {w : ℝ} {f g : Function Conf}
    (hfg : CalConf.SameBoundaryValueAtWeight w f g) :
    CalConf.SameBoundaryValue f g := by
  unfold SameBoundaryValueAtWeight at hfg
  unfold SameBoundaryValue EqModQ VanishesModQ
  rcases hfg with ⟨h, hdiff, _⟩
  exact ⟨h, hdiff⟩

theorem VanishesModQ_Qmul (h : Function Conf) :
    CalConf.VanishesModQ (CalConf.Qmul h) := by
  unfold VanishesModQ
  exact ⟨h, rfl⟩

theorem VanishesModQ_zero :
    CalConf.VanishesModQ (zero Conf) := by
  unfold VanishesModQ zero Qmul
  refine ⟨fun _ => 0, ?_⟩
  funext U
  simp

theorem EqModQ_iff_exists_Qmul (f g : Function Conf) :
    CalConf.EqModQ f g
      ↔
    ∃ h : Function Conf, (fun U => f U - g U) = CalConf.Qmul h := by
  rfl

theorem SameBoundaryValue_refl (f : Function Conf) :
    CalConf.SameBoundaryValue f f := by
  unfold SameBoundaryValue
  exact CalConf.EqModQ_refl f

theorem SameBoundaryValue_symm {f g : Function Conf}
    (hfg : CalConf.SameBoundaryValue f g) :
    CalConf.SameBoundaryValue g f := by
  unfold SameBoundaryValue EqModQ VanishesModQ at hfg ⊢
  rcases hfg with ⟨h, hh⟩
  refine ⟨fun U => - h U, ?_⟩
  funext U
  have hhU : f U - g U = CalConf.Q U * h U := by
    simpa [Qmul] using congrArg (fun F : Function Conf => F U) hh
  calc
    g U - f U = - (f U - g U) := by ring
    _ = - (CalConf.Q U * h U) := by rw [hhU]
    _ = CalConf.Q U * (- h U) := by ring

theorem SameBoundaryValue_trans {f g k : Function Conf}
    (hfg : CalConf.SameBoundaryValue f g)
    (hgk : CalConf.SameBoundaryValue g k) :
    CalConf.SameBoundaryValue f k := by
  unfold SameBoundaryValue EqModQ VanishesModQ at hfg hgk ⊢
  rcases hfg with ⟨h₁, hh₁⟩
  rcases hgk with ⟨h₂, hh₂⟩
  refine ⟨fun U => h₁ U + h₂ U, ?_⟩
  funext U
  have hh₁U : f U - g U = CalConf.Q U * h₁ U := by
    simpa [Qmul] using congrArg (fun F : Function Conf => F U) hh₁
  have hh₂U : g U - k U = CalConf.Q U * h₂ U := by
    simpa [Qmul] using congrArg (fun F : Function Conf => F U) hh₂
  calc
    f U - k U = (f U - g U) + (g U - k U) := by ring
    _ = CalConf.Q U * h₁ U + CalConf.Q U * h₂ U := by rw [hh₁U, hh₂U]
    _ = CalConf.Q U * (h₁ U + h₂ U) := by ring

theorem SameBoundaryValue_of_eq {f g : Function Conf}
    (h : f = g) :
    CalConf.SameBoundaryValue f g := by
  subst h
  exact CalConf.SameBoundaryValue_refl f


/-! ## Compatibility with pointwise algebra -/

theorem SameBoundaryValue_add {f₁ f₂ g₁ g₂ : Function Conf}
    (hf : CalConf.SameBoundaryValue f₁ f₂)
    (hg : CalConf.SameBoundaryValue g₁ g₂) :
    CalConf.SameBoundaryValue
      (add Conf f₁ g₁)
      (add Conf f₂ g₂) := by
  unfold SameBoundaryValue EqModQ VanishesModQ at hf hg ⊢
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  refine ⟨fun U => a U + b U, ?_⟩
  funext U
  have haU : f₁ U - f₂ U = CalConf.Q U * a U := by
    simpa [Qmul] using congrArg (fun F : Function Conf => F U) ha
  have hbU : g₁ U - g₂ U = CalConf.Q U * b U := by
    simpa [Qmul] using congrArg (fun F : Function Conf => F U) hb
  unfold add Qmul
  calc
    f₁ U + g₁ U - (f₂ U + g₂ U)
        = (f₁ U - f₂ U) + (g₁ U - g₂ U) := by ring
    _ = CalConf.Q U * a U + CalConf.Q U * b U := by rw [haU, hbU]
    _ = CalConf.Q U * (a U + b U) := by ring

theorem SameBoundaryValue_sub {f₁ f₂ g₁ g₂ : Function Conf}
    (hf : CalConf.SameBoundaryValue f₁ f₂)
    (hg : CalConf.SameBoundaryValue g₁ g₂) :
    CalConf.SameBoundaryValue
      (sub Conf f₁ g₁)
      (sub Conf f₂ g₂) := by
  unfold SameBoundaryValue EqModQ VanishesModQ at hf hg ⊢
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  refine ⟨fun U => a U - b U, ?_⟩
  funext U
  have haU : f₁ U - f₂ U = CalConf.Q U * a U := by
    simpa [Qmul] using congrArg (fun F : Function Conf => F U) ha
  have hbU : g₁ U - g₂ U = CalConf.Q U * b U := by
    simpa [Qmul] using congrArg (fun F : Function Conf => F U) hb
  unfold sub Qmul
  calc
    (f₁ U - g₁ U) - (f₂ U - g₂ U)
        = (f₁ U - f₂ U) - (g₁ U - g₂ U) := by ring
    _ = CalConf.Q U * a U - CalConf.Q U * b U := by rw [haU, hbU]
    _ = CalConf.Q U * (a U - b U) := by ring

theorem SameBoundaryValue_smul (c : ℝ) {f g : Function Conf}
    (hfg : CalConf.SameBoundaryValue f g) :
    CalConf.SameBoundaryValue
      (smul Conf c f)
      (smul Conf c g) := by
  unfold SameBoundaryValue EqModQ VanishesModQ at hfg ⊢
  rcases hfg with ⟨h, hh⟩
  refine ⟨fun U => c * h U, ?_⟩
  funext U
  have hhU : f U - g U = CalConf.Q U * h U := by
    simpa [Qmul] using congrArg (fun F : Function Conf => F U) hh
  unfold smul Qmul
  calc
    c * f U - c * g U = c * (f U - g U) := by ring
    _ = c * (CalConf.Q U * h U) := by rw [hhU]
    _ = CalConf.Q U * (c * h U) := by ring


/-! ## Ambient operators -/

/-- A formal ambient scalar operator. -/
abbrev Operator : Type _ :=
  Function Conf → Function Conf

/--
An ambient operator is tangential if it preserves the equivalence relation
given by equality modulo `Q`.
-/
def IsTangentialOperator (P : Operator (Conf := Conf)) : Prop :=
  ∀ {f g : Function Conf},
    CalConf.SameBoundaryValue f g →
      CalConf.SameBoundaryValue (P f) (P g)

/--
A weaker-looking but useful formulation: an operator preserves functions
vanishing modulo `Q`.

For a general nonlinear operator this is not equivalent to tangentiality.
The equivalence requires additivity/subtractivity assumptions.
-/
def PreservesVanishesModQ (P : Operator (Conf := Conf)) : Prop :=
  ∀ {f : Function Conf},
    CalConf.VanishesModQ f →
      CalConf.VanishesModQ (P f)

theorem IsTangentialOperator.id :
    CalConf.IsTangentialOperator (fun f : Function Conf => f) := by
  intro f g hfg
  exact hfg

theorem IsTangentialOperator.comp
    {P R : Operator (Conf := Conf)}
    (hP : CalConf.IsTangentialOperator P)
    (hR : CalConf.IsTangentialOperator R) :
    CalConf.IsTangentialOperator (fun f => P (R f)) := by
  intro f g hfg
  exact hP (hR hfg)


/-! ## Weighted tangentiality -/

/--
Tangentiality restricted to homogeneous functions of input weight `w`.

This is the right notion for ambient GJMS operators, because powers of the
ambient Laplacian are tangential only at the critical input weights.
-/
def IsTangentialAtWeight
    (P : Operator (Conf := Conf))
    (w : ℝ) : Prop :=
  ∀ {f g : Function Conf},
    CalConf.IsXHomogeneous w f →
    CalConf.IsXHomogeneous w g →
    CalConf.SameBoundaryValueAtWeight w f g →
      CalConf.SameBoundaryValue (P f) (P g)

/--
An operator maps homogeneous functions of weight `w₁` to homogeneous functions
of weight `w₂`.
-/
def MapsHomogeneousWeight
    (P : Operator (Conf := Conf))
    (w₁ w₂ : ℝ) : Prop :=
  ∀ {f : Function Conf},
    CalConf.IsXHomogeneous w₁ f →
      CalConf.IsXHomogeneous w₂ (P f)

/--
A weighted tangential ambient operator.

This is the structure which should eventually model an operator

`E[w₁] → E[w₂]`

defined by choosing an ambient extension, applying an ambient operator, and
restricting back to the boundary.
-/
structure WeightedTangentialOperator where
  inputWeight : ℝ
  outputWeight : ℝ
  toOperator : Operator (Conf := Conf)
  mapsWeight :
    CalConf.MapsHomogeneousWeight toOperator inputWeight outputWeight
  tangential :
    CalConf.IsTangentialAtWeight toOperator inputWeight


/-! ## GJMS weights -/

/-- The critical input weight for the `k`-th GJMS-type construction. -/
def criticalWeight (k : ℕ) : ℝ :=
  (k : ℝ) - CalConf.n / 2

/-- The output weight after applying `Δ̃^k` at the critical input weight. -/
def gjmsOutputWeight (k : ℕ) : ℝ :=
  - (k : ℝ) - CalConf.n / 2

/--
Weight bookkeeping for powers of the ambient Laplacian at the GJMS critical
weight.

This uses the already proved theorem `lapPow_isXHomogeneous` from
`Ambientoperator.lean`.
-/
theorem lapPow_has_GJMS_weight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    {f : Function Conf}
    (hf : CalConf.IsXHomogeneous (CalConf.criticalWeight k) f) :
    CalConf.IsXHomogeneous
      (CalConf.gjmsOutputWeight k)
      (CalConf.lapPow k f) := by
  have h := CalConf.lapPow_isXHomogeneous H k hf
  unfold LapPowHasWeight at h
  convert h using 1
  unfold criticalWeight gjmsOutputWeight
  ring

/--
The formal ambient `k`-th GJMS candidate, assuming tangentiality has been
proved separately.

At this abstraction level, the missing nontrivial theorem is exactly the
tangentiality of `Δ̃^k` at the critical weight.
-/
def ambientGJMSCandidate
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (htangential :
      CalConf.IsTangentialAtWeight
        (fun f : Function Conf => CalConf.lapPow k f)
        (CalConf.criticalWeight k)) :
    CalConf.WeightedTangentialOperator where
  inputWeight := CalConf.criticalWeight k
  outputWeight := CalConf.gjmsOutputWeight k
  toOperator := fun f => CalConf.lapPow k f
  mapsWeight := by
    intro f hf
    exact CalConf.lapPow_has_GJMS_weight H k hf
  tangential := htangential


/-!
## Future theorem

The main theorem to add later is:

```lean
theorem lapPow_isTangentialAtCriticalWeight
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ) :
    CalConf.IsTangentialAtWeight
      (fun f : Function Conf => CalConf.lapPow k f)
      (CalConf.criticalWeight k) := by
  ...
```
-/

end Calculus

end Operators
end Ambient
end ConformalStructure
