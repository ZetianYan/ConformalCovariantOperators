import Mathlib
import ExtrinsicGJMSOperators.Geometry.Conformal.Basic

/-!
# Density.lean

Abstract conformal densities built on top of `Basic.lean`.

Two equivalent viewpoints are implemented.

* `ScaleDependent.Density χ`: a family of scale-dependent representatives.
* `Equivariant.Density χ`: an equivariant function on the metric bundle.

The weight is encoded abstractly by a monoid homomorphism `χ : PosReal →* α`.
-/

open Classical

universe u v w

namespace ConformalStructure

/-The weight defined here is very general and it is regraded as a Monoid homogeneous. In other words, it maps positive real number to another algebraic structure. For specific density with weight w∈ ℝ, χ(r)=r^{w} -/
abbrev Weight (α : Type w) [Monoid α] := PosReal →* α

variable {M : Type u} (Conf : ConformalStructure.{u,v} M)
variable {α : Type w} [CommMonoid α]

/-- Rescaling a representative from `s₁` to `s₂`. -/
noncomputable def rescale (χ : Weight α) (s₁ s₂ : Conf.Scale) (f : M → α) : M → α :=
  fun x => χ (Conf.relativeFactor s₁ s₂ x) * f x

@[simp] theorem rescale_apply (χ : Weight α) (s₁ s₂ : Conf.Scale) (f : M → α) (x : M) :
    rescale Conf χ s₁ s₂ f x = χ (Conf.relativeFactor s₁ s₂ x) * f x := rfl

/-- A density described by its representative in every scale. -/
structure Density (χ : Weight α) where
  val : Conf.Scale → M → α
  compat : ∀ s₁ s₂ : Conf.Scale, val s₂ = rescale Conf χ s₁ s₂ (val s₁)

namespace Density

variable {χ : Weight α}
/-Here Coefun means coercion to function. In other words, we can regard a density as a function-/
instance : CoeFun (Density (Conf := Conf) χ) (fun _ => Conf.Scale → M → α) where
  coe d := d.val--Here the former Conf is the name of the structure and the later one is the name of the variable

@[simp] theorem compat_apply (d : Density (Conf := Conf) χ) (s₁ s₂ : Conf.Scale) (x : M) :
    d s₂ x = χ (Conf.relativeFactor s₁ s₂ x) * d s₁ x := by
  simpa [rescale] using congrFun (d.compat s₁ s₂) x

/-- The representative in a chosen scale. -/
def repr (d : Density (Conf := Conf) χ) (s : Conf.Scale) : M → α := d s

@[simp] theorem repr_apply
    (d : Density (Conf := Conf) χ) (s : Conf.Scale) (x : M) :
    repr (Conf := Conf) d s x = d s x := rfl



@[ext] theorem ext
    {d₁ d₂ : ConformalStructure.Density (Conf := Conf) χ}
    (h : ∀ s x, d₁.val s x = d₂.val s x) :
    d₁ = d₂ := by
  cases d₁ with
  | mk v₁ h₁ =>
    cases d₂ with
    | mk v₂ h₂ =>
      have hv : v₁ = v₂ := by
        funext s x
        exact h s x
      subst hv
      have : h₁ = h₂ := by
        apply Subsingleton.elim
      subst this
      rfl

end Density

namespace Equivariant

/-- An equivariant function on the metric bundle. -/
structure Density (χ : Weight α) where
  toFun : Conf.MetricBundle → α
  equivariant :
    ∀ (r : PosReal) (u : Conf.MetricBundle),
      toFun (Conf.dilateBundle r u) = χ r * toFun u



namespace Density

variable {χ : Weight α}

instance : CoeFun (Density (Conf := Conf) χ) (fun _ => Conf.MetricBundle → α) where
  coe d := d.toFun

@[simp] theorem equivariant_apply (d : Density (Conf := Conf) χ)
    (r : PosReal) (u : Conf.MetricBundle) :
    d (Conf.dilateBundle r u) = χ r * d u :=
  d.equivariant r u

@[ext] theorem ext
    {d₁ d₂ : Equivariant.Density (Conf := Conf) χ}
    (h : ∀ u : Conf.MetricBundle, d₁.toFun u = d₂.toFun u) :
    d₁ = d₂ := by
  cases d₁ with
  | mk f₁ h₁ =>
    cases d₂ with
    | mk f₂ h₂ =>
      have hf : f₁ = f₂ := funext h
      cases hf
      have hh : h₁ = h₂ := by
        apply Subsingleton.elim
      cases hh
      rfl


end Density
end Equivariant

section ComparisonLemmas

/-- Changing the reference scale changes the scale factor by the relative factor. -/
theorem scaleFactor_eq_mul_relativeFactor
    (s₁ s₂ : Conf.Scale) {x : M} (g : Conf.MetricFiber x) :
    Conf.scaleFactor s₁ g = Conf.scaleFactor s₂ g * Conf.relativeFactor s₁ s₂ x := by
  apply Conf.dilate_injective
  calc
    Conf.dilate (Conf.scaleFactor s₁ g) (s₁.metric x) = g := Conf.scaleFactor_spec s₁ g
    _ = Conf.dilate (Conf.scaleFactor s₂ g) (s₂.metric x) := by
          symm
          exact Conf.scaleFactor_spec s₂ g
    _ = Conf.dilate (Conf.scaleFactor s₂ g) (Conf.dilate (Conf.relativeFactor s₁ s₂ x) (s₁.metric x)) := by
          rw [Conf.relativeFactor_spec s₁ s₂ x]
    _ = Conf.dilate (Conf.scaleFactor s₂ g * Conf.relativeFactor s₁ s₂ x) (s₁.metric x) := by
          rw [Conf.dilate_mul]

@[simp] theorem scaleFactor_metric_of_scale
    (s₁ s₂ : Conf.Scale) (x : M) :
    Conf.scaleFactor s₁ (s₂.metric x) = Conf.relativeFactor s₁ s₂ x := rfl

@[simp] theorem relativeFactor_self (s : Conf.Scale) (x : M) :
    Conf.relativeFactor s s x = 1 := by
  apply Conf.dilate_injective (g := s.metric x)
  calc
    Conf.dilate (Conf.relativeFactor s s x) (s.metric x) = s.metric x :=
      Conf.relativeFactor_spec s s x
    _ = Conf.dilate 1 (s.metric x) := by
     rw [Conf.dilate_one]

@[simp] theorem scaleFactor_self_metric (s : Conf.Scale) (x : M) :
    Conf.scaleFactor s (s.metric x) = 1 := by
  rw [scaleFactor_metric_of_scale]
  exact Conf.relativeFactor_self s x

end ComparisonLemmas


namespace Density

variable {χ : Weight α}

/-- Convert a scale-dependent density to an equivariant function, using a chosen
reference scale. -/
noncomputable def toEquivariantUsing
    (d : Density (Conf := Conf) χ) (s₀ : Conf.Scale) :
    Equivariant.Density (Conf := Conf) χ where
  toFun u := by
    rcases u with ⟨x, g⟩
    exact χ (Conf.scaleFactor s₀ g) * d s₀ x
  equivariant := by
    intro r u
    rcases u with ⟨x, g⟩
    change χ (Conf.scaleFactor s₀ (Conf.dilate r g)) * d s₀ x =
      χ r * (χ (Conf.scaleFactor s₀ g) * d s₀ x)
    have hs : Conf.scaleFactor s₀ (Conf.dilate r g) = r * Conf.scaleFactor s₀ g := by
      apply Conf.dilate_injective
      calc
        Conf.dilate (Conf.scaleFactor s₀ (Conf.dilate r g)) (s₀.metric x) = Conf.dilate r g :=
          Conf.scaleFactor_spec s₀ (Conf.dilate r g)
        _ = Conf.dilate r (Conf.dilate (Conf.scaleFactor s₀ g) (s₀.metric x)) := by
              rw [Conf.scaleFactor_spec s₀ g]
        _ = Conf.dilate (r * Conf.scaleFactor s₀ g) (s₀.metric x) := by
              rw [Conf.dilate_mul]
    rw [hs, map_mul]
    simp [mul_assoc]

@[simp] theorem toEquivariantUsing_apply
    (d : Density (Conf := Conf) χ) (s₀ : Conf.Scale) (x : M) (g : Conf.MetricFiber x) :
    toEquivariantUsing (Conf := Conf) d s₀ ⟨x, g⟩  = χ (Conf.scaleFactor s₀ g) * d s₀ x := rfl

/-- The construction is independent of the chosen reference scale. -/
theorem toEquivariantUsing_independent
    (d : Density (Conf := Conf) χ) (s₀ s₁ : Conf.Scale) :
    toEquivariantUsing (Conf := Conf) d s₀ =
      toEquivariantUsing (Conf := Conf) d s₁ := by
  ext u
  rcases u with ⟨x, g⟩
  change χ (Conf.scaleFactor s₀ g) * d s₀ x =
    χ (Conf.scaleFactor s₁ g) * d s₁ x
  rw [Density.compat_apply (Conf := Conf) (χ := χ) d s₀ s₁ x]
  rw [Conf.scaleFactor_eq_mul_relativeFactor s₀ s₁ g]
  rw [map_mul]
  simp [mul_assoc, mul_left_comm, mul_comm]

 /-- Intrinsic conversion from scale-dependent to equivariant form.
This uses a chosen global scale. -/
noncomputable def toEquivariant
    (d : Density (Conf := Conf) χ) [Nonempty Conf.Scale] :
    Equivariant.Density (Conf := Conf) χ :=
  toEquivariantUsing (Conf := Conf) d (Classical.choice ‹Nonempty Conf.Scale›)

@[simp] theorem toEquivariant_apply_choice
    (d : Density (Conf := Conf) χ) [Nonempty Conf.Scale]
    (x : M) (g : Conf.MetricFiber x) :
    toEquivariant (Conf := Conf) d ⟨x, g⟩ =
      χ (Conf.scaleFactor (Classical.choice ‹Nonempty Conf.Scale›) g) *
        d (Classical.choice ‹Nonempty Conf.Scale›) x := rfl

theorem toEquivariant_apply
    (d : Density (Conf := Conf) χ) [Nonempty Conf.Scale]
    (s₀ : Conf.Scale) (x : M) (g : Conf.MetricFiber x) :
    toEquivariant (Conf := Conf) d ⟨x, g⟩ = χ (Conf.scaleFactor s₀ g) * d s₀ x := by
  classical
  unfold toEquivariant
  rw [toEquivariantUsing_independent (Conf := Conf) d
        (Classical.choice ‹Nonempty Conf.Scale›) s₀]
  rfl
end Density

namespace Equivariant

namespace Density

variable {χ : Weight α}

/-- Restrict an equivariant density to the section defined by a scale. -/
def toScaleDependent (d : Density (Conf := Conf) χ) :
    ConformalStructure.Density (Conf := Conf) χ where
  val s x := d ⟨x, s.metric x⟩
  compat := by
    intro s₁ s₂
    funext x
    change d ⟨x, s₂.metric x⟩ = χ (Conf.relativeFactor s₁ s₂ x) * d ⟨x, s₁.metric x⟩
    rw [← Conf.relativeFactor_spec s₁ s₂ x]
    simpa using d.equivariant (Conf.relativeFactor s₁ s₂ x) ⟨x, s₁.metric x⟩

@[simp] theorem toScaleDependent_apply
    (d : Density (Conf := Conf) χ) (s : Conf.Scale) (x : M) :
    toScaleDependent (Conf := Conf) d s x = d ⟨x, s.metric x⟩ := rfl

@[simp] theorem toEquivariant_toScaleDependent
    (d : Equivariant.Density (Conf := Conf) χ) [Nonempty Conf.Scale] :
    Density.toEquivariant (Conf := Conf)
      (Equivariant.Density.toScaleDependent (Conf := Conf) d) = d := by
  classical
  ext u
  rcases u with ⟨x, g⟩
  let s₀ : Conf.Scale := Classical.choice ‹Nonempty Conf.Scale›
  change χ (Conf.scaleFactor s₀ g) * d ⟨x, s₀.metric x⟩ = d ⟨x, g⟩
  rw [← Conf.scaleFactor_spec s₀ g]
  simpa using (d.equivariant (Conf.scaleFactor s₀ g) ⟨x, s₀.metric x⟩).symm

end Density
end Equivariant


namespace Density

variable {χ : Weight α}

@[simp] theorem toScaleDependent_toEquivariantUsing
    (d : Density (Conf := Conf) χ) (s₀ s : Conf.Scale) (x : M) :
    (Equivariant.Density.toScaleDependent
      (Conf := Conf) (χ := χ)
      (Density.toEquivariantUsing
        (Conf := Conf) (χ := χ) d s₀)) s x
      = d s x := by
  change χ (Conf.scaleFactor s₀ (s.metric x)) * d s₀ x = d s x
  rw [Conf.scaleFactor_metric_of_scale]
  symm
  exact Density.compat_apply (Conf := Conf) (χ := χ) d s₀ s x

@[simp] theorem toScaleDependent_toEquivariant
    (d : Density (Conf := Conf) χ) [Nonempty Conf.Scale]
    (s : Conf.Scale) (x : M) :
    (Equivariant.Density.toScaleDependent
      (Conf := Conf) (χ := χ)
      (Density.toEquivariant
        (Conf := Conf) (χ := χ) d)) s x
      = d s x := by
  classical
  simpa [Density.toEquivariant]
    using
      (Density.toScaleDependent_toEquivariantUsing
        (Conf := Conf) (χ := χ)
        d (Classical.choice ‹Nonempty Conf.Scale›) s x)

end Density

namespace Equivariant
namespace Density

variable {χ : Weight α}

/-- Equivalence between the two descriptions of densities, once a global scale exists. -/
noncomputable def equivScaleDependentEquiv [Nonempty Conf.Scale] :
    ConformalStructure.Equivariant.Density (Conf := Conf) χ ≃
      ConformalStructure.Density (Conf := Conf) χ where
  toFun := fun d =>
    ConformalStructure.Equivariant.Density.toScaleDependent (Conf := Conf) (χ := χ) d
  invFun := fun d =>
    ConformalStructure.Density.toEquivariant (Conf := Conf) (χ := χ) d
  left_inv := by
    intro d
    simpa using
      (ConformalStructure.Equivariant.Density.toEquivariant_toScaleDependent
        (Conf := Conf) (χ := χ) d)
  right_inv := by
    intro d
    ext s x
    simpa using
      (ConformalStructure.Density.toScaleDependent_toEquivariant
        (Conf := Conf) (χ := χ) d s x)

end Density
end Equivariant

end ConformalStructure
