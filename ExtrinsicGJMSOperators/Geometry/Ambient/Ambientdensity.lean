import Mathlib
import ExtrinsicGJMSOperators.Geometry.Conformal.Basic
import ExtrinsicGJMSOperators.Geometry.Conformal.Density
import ExtrinsicGJMSOperators.Geometry.Ambient.Ambientbasic

open Classical

universe u v w

namespace ConformalStructure

variable {M : Type u} (Conf : ConformalStructure.{u,v} M)
variable {α : Type w} [CommMonoid α]

abbrev AmbientWeight := ConformalStructure.Weight (α := α)

namespace Ambient
namespace Equivariant

/-- An ambient density is an equivariant function on the ambient bundle. -/
structure Density (χ : Weight α) where
  toFun : Conf.AmbientBundle → α
  equivariant :
    ∀ (r : PosReal) (U : Conf.AmbientBundle),
      toFun (Conf.ambientDilate r U) = χ r * toFun U

namespace Density

variable {χ : Weight α}

instance : CoeFun (Density (Conf := Conf) χ) (fun _ => Conf.AmbientBundle → α) where
  coe d := d.toFun

@[simp] theorem equivariant_apply
    (d : Density (Conf := Conf) χ) (r : PosReal) (U : Conf.AmbientBundle) :
    d (Conf.ambientDilate r U) = χ r * d U :=
  d.equivariant r U

@[ext] theorem ext
    {d₁ d₂ : Density (Conf := Conf) χ}
    (h : ∀ U : Conf.AmbientBundle, d₁.toFun U = d₂.toFun U) :
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

/-- Restriction of an ambient density to the hypersurface `ρ = 0`. -/
def restrictToBoundary
    (d : Density (Conf := Conf) χ) :
    ConformalStructure.Equivariant.Density (Conf := Conf) χ where
  toFun := fun u => d.toFun (Conf.iota u)
  equivariant := by
    intro r u
    simpa [ConformalStructure.iota, ConformalStructure.ambientDilate,
      ConformalStructure.dilateBundle] using
      d.equivariant r (Conf.iota u)

@[simp] theorem restrictToBoundary_apply
    (d : Density (Conf := Conf) χ) (u : Conf.MetricBundle) :
    (restrictToBoundary (d := d)) u = d (Conf.iota u) := by
  rfl

@[simp] theorem restrictToBoundary_apply_mk
    (d : Density (Conf := Conf) χ) (x : M) (g : Conf.MetricFiber x) :
    (restrictToBoundary (d := d)) ⟨x, g⟩ = d ((⟨x, g⟩), (0 : ℝ)) := by
  rfl

/-- Restriction to the boundary, evaluated on the section of a chosen scale. -/
def restrictToScaleDependent
    (d : Density (Conf := Conf) χ) :
    ConformalStructure.Density (Conf := Conf) χ :=
  (restrictToBoundary (d := d)).toScaleDependent

@[simp] theorem restrictToScaleDependent_apply
    (d : Density (Conf := Conf) χ) (s : Conf.Scale) (x : M) :
    (restrictToScaleDependent (d := d)) s x = d ((⟨x, s.metric x⟩), (0 : ℝ)) := by
  rfl

end Density
end Equivariant


/-!  ## Optional: concrete ambient densities on actual metrics -/

namespace ConcreteEquivariant

/-- A concrete ambient density is an equivariant function on the concrete ambient bundle. -/
structure Density (χ : Weight α) where
  toFun : Conf.AmbientPointMetricBundle → α
  equivariant :
    ∀ (r : PosReal) (U : Conf.AmbientPointMetricBundle),
      toFun (Conf.ambientPointDilate r U) = χ r * toFun U

namespace Density

variable {χ : Weight α}

instance : CoeFun (Density (Conf := Conf) χ)
    (fun _ => Conf.AmbientPointMetricBundle → α) where
  coe d := d.toFun

@[simp] theorem equivariant_apply
    (d : Density (Conf := Conf) χ) (r : PosReal) (U : Conf.AmbientPointMetricBundle) :
    d (Conf.ambientPointDilate r U) = χ r * d U :=
  d.equivariant r U

@[ext] theorem ext
    {d₁ d₂ : Density (Conf := Conf) χ}
    (h : ∀ U : Conf.AmbientPointMetricBundle, d₁.toFun U = d₂.toFun U) :
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
end ConcreteEquivariant

end Ambient
end ConformalStructure
