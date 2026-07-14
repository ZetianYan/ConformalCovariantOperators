import ConformalCovariantOperators.Conformal.Basic
universe u v

namespace ConformalStructure

variable {M : Type u} (Conf : ConformalStructure M)

/-!
# Ambient basic objects

This file introduces the minimal ambient-space layer built on top of `Basic.lean`.

The guiding principle is:

- `MetricBundle` is the ray bundle associated to the initial conformal structure;
- the ambient space is `MetricBundle × ℝ`, where the extra `ℝ`-coordinate is `ρ`;
- a straight-form ambient metric is encoded only as formal data:
  a base scale together with a 1-parameter family `gRho : ℝ → MetricField`.

At this stage we do **not** define an actual pseudo-Riemannian tensor
`2ρ dt² + 2t dt dρ + t² gρ`; we only package the data needed for it.
-/


/-! ## Ambient total spaces -/

/-- The ambient extension of the ray bundle by one real `ρ`-coordinate. -/
def AmbientBundle := Conf.MetricBundle × ℝ

/-- A concrete ambient bundle using actual pointwise metrics instead of rays. -/
def AmbientPointMetricBundle := Conf.PointMetricBundle × ℝ

/-- Projection from the ambient bundle to the base manifold. -/
def ambientProj : Conf.AmbientBundle → M
  | (u, _) => u.1

/-- Projection from the concrete ambient bundle to the base manifold. -/
def ambientPointProj : Conf.AmbientPointMetricBundle → M
  | (u, _) => u.1

/-- The `ρ`-coordinate on the ambient bundle. -/
def rhoCoord : Conf.AmbientBundle → ℝ
  | (_, ρ) => ρ

/-- The `ρ`-coordinate on the concrete ambient bundle. -/
def rhoPointCoord : Conf.AmbientPointMetricBundle → ℝ
  | (_, ρ) => ρ

/-- Inclusion of the ray bundle as the hypersurface `{ρ = 0}`. -/
def iota : Conf.MetricBundle → Conf.AmbientBundle :=
  fun u => (u, 0)

/-- Inclusion of the concrete metric bundle as the hypersurface `{ρ = 0}`. -/
def iotaPoint : Conf.PointMetricBundle → Conf.AmbientPointMetricBundle :=
  fun u => (u, 0)

/-- Ambient dilation on the ray bundle side: act on the ray factor, keep `ρ` fixed. -/
def ambientDilate (a : PosReal) : Conf.AmbientBundle → Conf.AmbientBundle
  | (u, ρ) => (Conf.dilateBundle a u, ρ)

/-- Ambient dilation on the concrete metric side: act on the metric factor, keep `ρ` fixed. -/
def ambientPointDilate (a : PosReal) :
    Conf.AmbientPointMetricBundle → Conf.AmbientPointMetricBundle
  | (u, ρ) => (Conf.dilatePointMetricBundle a u, ρ)

/-- Projection from concrete ambient metrics to ambient rays. -/
def ambientPointToFiber : Conf.AmbientPointMetricBundle → Conf.AmbientBundle
  | (u, ρ) => (Conf.pointToFiberBundle u, ρ)


/-! ## Basic simp lemmas -/

@[simp] theorem ambientProj_iota (u : Conf.MetricBundle) :
    Conf.ambientProj (Conf.iota u) = u.1 := rfl

@[simp] theorem ambientPointProj_iotaPoint (u : Conf.PointMetricBundle) :
    Conf.ambientPointProj (Conf.iotaPoint u) = u.1 := rfl

@[simp] theorem rhoCoord_iota (u : Conf.MetricBundle) :
    Conf.rhoCoord (Conf.iota u) = 0 := rfl

@[simp] theorem rhoPointCoord_iotaPoint (u : Conf.PointMetricBundle) :
    Conf.rhoPointCoord (Conf.iotaPoint u) = 0 := rfl

@[simp] theorem ambientProj_ambientDilate (a : PosReal) (u : Conf.AmbientBundle) :
    Conf.ambientProj (Conf.ambientDilate a u) = Conf.ambientProj u := by
  cases u
  rfl

@[simp] theorem rhoCoord_ambientDilate (a : PosReal) (u : Conf.AmbientBundle) :
    Conf.rhoCoord (Conf.ambientDilate a u) = Conf.rhoCoord u := by
  cases u with
  | mk u ρ =>
      simp [ambientDilate, rhoCoord]

@[simp] theorem ambientPointProj_ambientPointDilate
    (a : PosReal) (u : Conf.AmbientPointMetricBundle) :
    Conf.ambientPointProj (Conf.ambientPointDilate a u) = Conf.ambientPointProj u := by
  cases u
  rfl

@[simp] theorem rhoPointCoord_ambientPointDilate
    (a : PosReal) (u : Conf.AmbientPointMetricBundle) :
    Conf.rhoPointCoord (Conf.ambientPointDilate a u) = Conf.rhoPointCoord u := by
  cases u with
  | mk u ρ =>
      simp [ambientPointDilate, rhoPointCoord]

@[simp] theorem ambientPointToFiber_iotaPoint (u : Conf.PointMetricBundle) :
    Conf.ambientPointToFiber (Conf.iotaPoint u) = Conf.iota (Conf.pointToFiberBundle u) := rfl

@[simp] theorem ambientPointToFiber_ambientPointDilate
    (a : PosReal) (u : Conf.AmbientPointMetricBundle) :
    Conf.ambientPointToFiber (Conf.ambientPointDilate a u)
      = Conf.ambientDilate a (Conf.ambientPointToFiber u) := by
  cases u with
  | mk u ρ =>
      simp [ambientPointToFiber, ambientPointDilate, ambientDilate,
        ConformalStructure.pointToFiberBundle_dilate]


/-! ## Ambient trivialization induced by a scale -/

/--
Given a scale `s`, the existing trivialization of the ray bundle extends to the
ambient bundle by adjoining the `ρ`-coordinate.

We use the target `((PosReal × M) × ℝ)` to avoid ambiguity in product associativity.
-/
noncomputable def ambientTrivialization (s : Conf.Scale) :
    Conf.AmbientBundle ≃ ((PosReal × M) × ℝ) where
  toFun := fun U =>
    (((Conf.trivialization s U.1).1, (Conf.trivialization s U.1).2), U.2)
  invFun := fun V =>
    ((Conf.trivialization s).symm V.1, V.2)
  left_inv := by
    intro U
    cases U
    simp
  right_inv := by
    intro V
    cases V
    simp

/-- The ambient trivialization sends the hypersurface `{ρ = 0}` to `{ρ = 0}`. -/
@[simp] theorem ambientTrivialization_iota
    (s : Conf.Scale) (u : Conf.MetricBundle) :
    Conf.ambientTrivialization s (Conf.iota u)
      = (((Conf.trivialization s u).1, (Conf.trivialization s u).2), 0) := rfl


/-! ## Straight-form ambient data -/

/--
A 1-parameter family of actual metrics on `M`, anchored at a chosen base scale.

Important:
`gRho ρ` is a family of **concrete metric fields**, not a family of scales.
Only at `ρ = 0` do we require compatibility with the initial conformal structure.
-/
structure StraightMetricData where
  /-- The chosen background scale corresponding to `g₀`. -/
  baseScale : Conf.Scale

  /-- A 1-parameter family of concrete metrics on `M`. -/
  gRho : ℝ → Conf.MetricField

  /-- Compatibility at `ρ = 0`: `gRho 0` projects to the ray section of `baseScale`. -/
  compat0 : ∀ x : M, Conf.toFiber (gRho 0 x) = baseScale.metric x

namespace StraightMetricData

variable {Conf}

/-- The concrete metric field at `ρ = 0`. -/
def g0 (A : Conf.StraightMetricData) : Conf.MetricField := A.gRho 0

@[simp] theorem g0_apply (A : Conf.StraightMetricData) (x : M) :
    A.g0 x = A.gRho 0 x := rfl

@[simp] theorem toFiber_g0 (A : Conf.StraightMetricData) (x : M) :
    Conf.toFiber (A.g0 x) = A.baseScale.metric x :=
  A.compat0 x

/-- The ray section underlying the base scale. -/
def baseRaySection (A : Conf.StraightMetricData) : ∀ x : M, Conf.MetricFiber x :=
  A.baseScale.metric

@[simp] theorem baseRaySection_apply (A : Conf.StraightMetricData) (x : M) :
    A.baseRaySection x = A.baseScale.metric x := rfl

end StraightMetricData


/--
A formal straight-form ambient metric.

At the current abstraction level, this is just a wrapper around the data needed
to write the expression
`2ρ dt² + 2t dt dρ + t² gρ`
after choosing a scale trivialization.
-/
structure StraightForm where
  data : Conf.StraightMetricData

namespace StraightForm

variable {Conf}

/-- The underlying base scale. -/
def baseScale (G : Conf.StraightForm) : Conf.Scale := G.data.baseScale

/-- The underlying 1-parameter family of concrete metrics. -/
def gRho (G : Conf.StraightForm) : ℝ → Conf.MetricField := G.data.gRho

@[simp] theorem compat0 (G : Conf.StraightForm) (x : M) :
    Conf.toFiber (G.gRho 0 x) = G.baseScale.metric x :=
  G.data.compat0 x

end StraightForm


/-! ## Optional helper constructors -/

/-- Build a straight form directly from its data. -/
def mkStraightForm (A : Conf.StraightMetricData) : Conf.StraightForm :=
  ⟨A⟩

@[simp] theorem mkStraightForm_data (A : Conf.StraightMetricData) :
    (Conf.mkStraightForm A).data = A := rfl


/-
  ------------------------------------------------------------
  Suggested next step
  ------------------------------------------------------------

  Once you define ambient densities on `Conf.AmbientBundle`, this file will be
  enough to support:
  - restriction to `ρ = 0`,
  - tangential operators,
  - and later a chosen-scale expression of straight form.

  At that stage one can add:
  - `Ambient.Density`
  - restriction `Ē[w] → E[w]`
  - abstract tangential operators
  - and then specific ambient operators.
-/

end ConformalStructure
