import Mathlib

/-!
# Conformal/Basic.lean

A first intrinsic skeleton for conformal structures in Lean.

Design philosophy:

* A conformal structure is encoded intrinsically, without choosing a preferred metric.
* The "metric bundle" is modeled abstractly as a family of fibers carrying a free and
  transitive action of positive reals.
* A `Scale` is a global section of this bundle.
* Once a scale is chosen, the metric bundle becomes trivial:
    MetricBundle ≃ PosReal × M

This file is intentionally abstract.  It does **not yet** identify the fibers with
rays inside `S^2 T^* M`; that can be added later after deciding how to model
Riemannian metrics/tensors over manifolds in mathlib.
-/

open Classical

universe u v

abbrev PosReal := Units NNReal--Here Units NNReal contain all invertible non-negative real numbers which are exactly what we want.

/-- A bare structure encoding the existence of concrete metrics on `M`.

`PointMetric x` is the type of actual metrics at the point `x`.
A global metric field is then a section `∀ x, PointMetric x`.
-/
class MetricStructure (M : Type u) where
  PointMetric : M → Type v


namespace MetricStructure

variable {M : Type u} (Met : MetricStructure M)

/-- A global metric field is simply a section of pointwise metrics. -/
def MetricField := ∀ x : M, Met.PointMetric x

end MetricStructure


/-- An intrinsic conformal structure on `M`.

For each `x : M`, the fiber `MetricFiber x` should be thought of as the ray of metrics
at `x` inside the conformal class.  The action of `PosReal` is the dilation
`g ↦ r^2 g` in the geometric picture; here we suppress the square and use a single
positive parameter abstractly.
-/
structure ConformalStructure (M : Type u) extends MetricStructure M where
  MetricFiber : M → Type v

  /-- Send an actual pointwise metric to its ray class. -/
  toFiber : ∀ {x : M}, PointMetric x → MetricFiber x

  /-- Positive dilations on each fiber. -/
  dilate : ∀ {x : M}, PosReal → MetricFiber x → MetricFiber x

  /-- Identity dilation. -/
  dilate_one : ∀ {x : M} (g : MetricFiber x), dilate 1 g = g

  /-- Compatibility with multiplication. -/
  dilate_mul :
    ∀ {x : M} (a b : PosReal) (g : MetricFiber x),
      dilate (a * b) g = dilate a (dilate b g)

  /-- Transitivity of the positive dilation action on each fiber. -/
  dilate_exists :
    ∀ {x : M} (g h : MetricFiber x), ∃ r : PosReal, dilate r g = h

  /-- Freeness of the positive dilation action on each fiber. -/
  dilate_injective :
    ∀ {x : M} {g : MetricFiber x} {r s : PosReal},
      dilate r g = dilate s g → r = s

  /-- Concrete dilation on actual metrics. -/
  dilateMetric : ∀ {x : M}, PosReal → PointMetric x → PointMetric x

  /- Concrete metric-level axioms -/
  dilateMetric_one :
    ∀ {x : M} (g : PointMetric x), dilateMetric 1 g = g

  dilateMetric_mul :
    ∀ {x : M} (a b : PosReal) (g : PointMetric x),
      dilateMetric (a * b) g = dilateMetric a (dilateMetric b g)

  dilateMetric_injective :
    ∀ {x : M} (a : PosReal), Function.Injective (dilateMetric (x := x) a)

  /-- Compatibility: projecting after concrete dilation agrees with
  dilating in the ray bundle after projection. -/
  toFiber_dilateMetric :
    ∀ {x : M} (a : PosReal) (g : PointMetric x),
      toFiber (dilateMetric a g) = dilate a (toFiber g)

namespace ConformalStructure

variable {M : Type u} (Conf : ConformalStructure M)

def PointwiseMetric (x : M) := Conf.PointMetric x
def MetricField := ∀ x : M, Conf.PointMetric x


/-- The total space of the metric bundle associated to a conformal structure. -/
def PointMetricBundle := Σ x : M, Conf.PointMetric x
def MetricBundle := Σ x : M, Conf.MetricFiber x

/-- Projection from the metric bundle to the base manifold. -/
def proj (u : MetricBundle Conf) : M := u.1

def pointproj (u : PointMetricBundle Conf) : M := u.1

@[simp] theorem proj_mk (x : M) (g : Conf.MetricFiber x) :
    proj Conf ⟨x, g⟩ = x := rfl

@[simp] theorem pointproj_mk (x : M) (g : Conf.PointMetric x) :
    pointproj Conf ⟨x, g⟩ = x := rfl

/-- Dilation on the total space of the metric bundle. -/
def dilateBundle (r : PosReal) : Conf.MetricBundle → Conf.MetricBundle
  | ⟨x, g⟩ => ⟨x, Conf.dilate r g⟩

/-- Dilation on the concrete metric bundle. -/
def dilatePointMetricBundle (a : PosReal) : Conf.PointMetricBundle → Conf.PointMetricBundle
  | ⟨x, g⟩ => ⟨x, Conf.dilateMetric a g⟩

@[simp] theorem dilateBundle_proj (r : PosReal) (u : Conf.MetricBundle) :
    Conf.proj (Conf.dilateBundle r u) = Conf.proj u := by
  cases u
  rfl

@[simp] theorem dilatePointMetricBundle_proj (r : PosReal) (u : Conf.PointMetricBundle) :
    Conf.pointproj (Conf.dilatePointMetricBundle r u) = Conf.pointproj u := by
  cases u
  rfl


@[simp] theorem dilateBundle_mk (r : PosReal) (x : M) (g : Conf.MetricFiber x) :
    Conf.dilateBundle r ⟨x, g⟩ = ⟨x, Conf.dilate r g⟩ := rfl

@[simp] theorem dilatePointMetricBundle_mk (r : PosReal) (x : M) (g : Conf.PointMetric x) :
    Conf.dilatePointMetricBundle r ⟨x, g⟩ = ⟨x, Conf.dilateMetric r g⟩ := rfl

/-- A scale is a choice of one point in each conformal ray, i.e. a representative
metric in the conformal class. -/
structure Scale where
  totalmetric : Conf.MetricField
  metric : ∀ x : M, Conf.MetricFiber x
  compat : ∀ x : M, Conf.toFiber (totalmetric x) = metric x



/-- The induced section of the metric bundle. -/
def Scale.section {M : Type u} {Conf : ConformalStructure M}
    (s : ConformalStructure.Scale Conf) :
    M → ConformalStructure.MetricBundle Conf :=
  fun x => ⟨x, s.metric x⟩

@[simp] theorem Scale.proj_section {M : Type u} {Conf : ConformalStructure M}
    (s : ConformalStructure.Scale Conf) (x : M) :
    ConformalStructure.proj Conf (Scale.section s x) = x := rfl

/-- The positive dilation factor taking the chosen scale to a given point in the same fiber. -/
noncomputable def scaleFactor (s : ConformalStructure.Scale Conf) {x : M} (g : Conf.MetricFiber x) : PosReal :=
  Classical.choose (Conf.dilate_exists (s.metric x) g)

@[simp] theorem scaleFactor_spec (s : ConformalStructure.Scale Conf) {x : M} (g : Conf.MetricFiber x) :
    Conf.dilate (Conf.scaleFactor s g) (s.metric x) = g :=
  Classical.choose_spec (Conf.dilate_exists (s.metric x) g)

/-- The trivialization of the metric bundle induced by a scale:
    each point of the bundle is uniquely `(r, x)` with `g = r • s(x)`. -/
noncomputable def trivialization (s : ConformalStructure.Scale Conf) : Conf.MetricBundle ≃ PosReal × M where
  toFun u := by
    rcases u with ⟨x, g⟩
    exact (Conf.scaleFactor s g, x)
  invFun p := ⟨p.2, Conf.dilate p.1 (s.metric p.2)⟩
  left_inv u := by
    rcases u with ⟨x, g⟩
    change Sigma.mk x (Conf.dilate (Conf.scaleFactor s g) (s.metric x)) = Sigma.mk x g
    simp [Conf.scaleFactor_spec]
  right_inv p := by
    rcases p with ⟨r, x⟩
    change (Conf.scaleFactor s (Conf.dilate r (s.metric x)), x) = (r, x)
    have h1 : Conf.dilate (Conf.scaleFactor s (Conf.dilate r (s.metric x))) (s.metric x) =
        Conf.dilate r (s.metric x) := by
      exact Conf.scaleFactor_spec s (Conf.dilate r (s.metric x))
    have h2 : Conf.scaleFactor s (Conf.dilate r (s.metric x)) = r := by
      exact Conf.dilate_injective h1
    simp [h2]

@[simp] theorem trivialization_apply (s : ConformalStructure.Scale Conf) (x : M) (g : Conf.MetricFiber x) :
    Conf.trivialization s ⟨x, g⟩ = (Conf.scaleFactor s g, x) := rfl

@[simp] theorem trivialization_symm_apply (s : Conf.Scale) (r : PosReal) (x : M) :
    (Conf.trivialization s).symm (r, x) = ⟨x, Conf.dilate r (s.metric x)⟩ := rfl

/-- The fiber over a point is nonempty once a scale is chosen. -/
theorem fiber_nonempty (s : ConformalStructure.Scale Conf) (x : M) : Nonempty (Conf.MetricFiber x) :=
  ⟨s.metric x⟩

/-- Any two scales differ by a unique positive function on `M`. -/
noncomputable def relativeFactor (s₁ s₂ : Conf.Scale) : M → PosReal :=
  fun x => Conf.scaleFactor s₁ (s₂.metric x)

@[simp] theorem relativeFactor_spec (s₁ s₂ : Conf.Scale) (x : M) :
    Conf.dilate (Conf.relativeFactor s₁ s₂ x) (s₁.metric x) = s₂.metric x :=
  Conf.scaleFactor_spec s₁ (s₂.metric x)

/-- Reconstructing one scale from another and the relative positive function. -/
theorem scale_eq_dilate_relativeFactor (s₁ s₂ : Conf.Scale) :
    s₂.metric = fun x => Conf.dilate (Conf.relativeFactor s₁ s₂ x) (s₁.metric x) := by
  funext x
  exact (Conf.relativeFactor_spec s₁ s₂ x).symm

/-- Projection from concrete metric bundle to ray bundle. -/
def pointToFiberBundle : Conf.PointMetricBundle → Conf.MetricBundle
  | ⟨x, g⟩ => ⟨x, Conf.toFiber g⟩

@[simp] theorem pointToFiberBundle_dilate
    (a : PosReal) (u : Conf.PointMetricBundle) :
    Conf.pointToFiberBundle (Conf.dilatePointMetricBundle a u)
      = Conf.dilateBundle a (Conf.pointToFiberBundle u) := by
  cases u with
  | mk x g =>
      simp [pointToFiberBundle, dilatePointMetricBundle, dilateBundle,
        Conf.toFiber_dilateMetric]

/-- Concrete dilation of a metric field by a positive function. -/
def dilateMetricField (σ : M → PosReal) (g : Conf.MetricField) : Conf.MetricField :=
  fun x => Conf.dilateMetric (σ x) (g x)

/-- Constant dilation of a metric field. -/
def dilateMetricFieldConst (a : PosReal) (g : Conf.MetricField) : Conf.MetricField :=
  fun x => Conf.dilateMetric a (g x)

@[simp] theorem toFiber_dilateMetricField
    (σ : M → PosReal) (g : Conf.MetricField) (x : M) :
    Conf.toFiber (Conf.dilateMetricField σ g x)
      = Conf.dilate (σ x) (Conf.toFiber (g x)) := by
  simp [dilateMetricField, Conf.toFiber_dilateMetric]

@[simp] theorem toFiber_dilateMetricFieldConst
    (a : PosReal) (g : Conf.MetricField) (x : M) :
    Conf.toFiber (Conf.dilateMetricFieldConst a g x)
      = Conf.dilate a (Conf.toFiber (g x)) := by
  simp [dilateMetricFieldConst, Conf.toFiber_dilateMetric]


/-- If you want a scale obtained from constant dilation of a concrete representative. -/
def Scale.dilateTotalMetric (s : Conf.Scale) (a : PosReal) : Conf.Scale where
  totalmetric := Conf.dilateMetricFieldConst a s.totalmetric
  metric := fun x => Conf.dilate a (s.metric x)
  compat := by
    intro x
    calc
      Conf.toFiber (Conf.dilateMetricFieldConst a s.totalmetric x)
          = Conf.dilate a (Conf.toFiber (s.totalmetric x)) := by
              simp [ConformalStructure.dilateMetricFieldConst, Conf.toFiber_dilateMetric]
      _ = Conf.dilate a (s.metric x) := by
              rw [s.compat x]

end ConformalStructure

/-!
## Notes for future extensions

1. The next step is to realize `MetricFiber x` concretely as a ray in the space of
   positive-definite symmetric bilinear forms on `T_x M`.

2. After that, define density bundles `E[w]` either:
   * abstractly from the metric bundle via equivariance, or
   * more pragmatically first, using the scale-change law.

3. Only after densities are in place does it become natural to formalize conformally
   invariant differential operators such as the Yamabe operator, Paneitz operator,
   GJMS operators, and eventually the polydifferential operators in the paper.
-/
