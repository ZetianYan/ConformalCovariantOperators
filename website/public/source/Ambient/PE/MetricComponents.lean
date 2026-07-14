import ConformalCovariantOperators.Ambient.PE.NormalForm

open Classical
open scoped BigOperators

noncomputable section

universe u w

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Poincare metric components

This file realizes

`gPlus = r^(-2) (dr^2 + h_r)`

and its inverse in radial-tangential coordinates.
-/

/-- Radial and tangential indices in Poincare normal form. -/
inductive PEIndex (Iota : Type u) where
  | radial : PEIndex Iota
  | tangential : Iota -> PEIndex Iota
deriving Repr, DecidableEq, Fintype

namespace PEIndex

variable {Iota : Type u}

/-- The Kronecker delta on PE normal-form indices. -/
def kronecker [DecidableEq Iota] (I J : PEIndex Iota) : Real :=
  if I = J then 1 else 0

@[simp]
theorem kronecker_self [DecidableEq Iota] (I : PEIndex Iota) :
    kronecker I I = 1 := by
  simp [kronecker]

@[simp]
theorem kronecker_radial_tangential
    [DecidableEq Iota]
    (i : Iota) :
    kronecker radial (tangential i) = 0 := by
  simp [kronecker]

@[simp]
theorem kronecker_tangential_radial
    [DecidableEq Iota]
    (i : Iota) :
    kronecker (tangential i) radial = 0 := by
  simp [kronecker]

/-- PE indices are equivalent to an optional tangential index. -/
def equivOption : PEIndex Iota ≃ Option Iota where
  toFun
    | radial => none
    | tangential i => some i
  invFun
    | none => radial
    | some i => tangential i
  left_inv := by
    intro I
    cases I <;> rfl
  right_inv := by
    intro I
    cases I <;> rfl

/-- Split a finite PE-index sum into radial and tangential parts. -/
theorem sum_index
    {R : Type w}
    [Fintype Iota]
    [AddCommMonoid R]
    (f : PEIndex Iota -> R) :
    (∑ I : PEIndex Iota, f I)
      =
    f radial + ∑ i : Iota, f (tangential i) := by
  classical
  calc
    (∑ I : PEIndex Iota, f I)
        = ∑ o : Option Iota, f (equivOption.symm o) := by
            apply Fintype.sum_equiv equivOption
            intro I
            simp
    _ = f radial + ∑ i : Iota, f (tangential i) := by
          rw [Fintype.sum_option]
          rfl

end PEIndex

/-- Boundary metric components and their formal inverse at a fixed radius. -/
structure PENormalMetricComponents (Iota : Type u) where
  r : Real
  h : Iota -> Iota -> Real
  hInv : Iota -> Iota -> Real

/-- Covariant components of `gPlus`. -/
def gPlusDown (C : PENormalMetricComponents Iota) :
    PEIndex Iota -> PEIndex Iota -> Real
  | PEIndex.radial, PEIndex.radial => (C.r ^ 2)⁻¹
  | PEIndex.radial, PEIndex.tangential _ => 0
  | PEIndex.tangential _, PEIndex.radial => 0
  | PEIndex.tangential i, PEIndex.tangential j =>
      (C.r ^ 2)⁻¹ * C.h i j

/-- Contravariant components of `gPlus`. -/
def gPlusUp (C : PENormalMetricComponents Iota) :
    PEIndex Iota -> PEIndex Iota -> Real
  | PEIndex.radial, PEIndex.radial => C.r ^ 2
  | PEIndex.radial, PEIndex.tangential _ => 0
  | PEIndex.tangential _, PEIndex.radial => 0
  | PEIndex.tangential i, PEIndex.tangential j =>
      C.r ^ 2 * C.hInv i j

@[simp]
theorem gPlusDown_radial_radial (C : PENormalMetricComponents Iota) :
    gPlusDown C PEIndex.radial PEIndex.radial = (C.r ^ 2)⁻¹ := rfl

@[simp]
theorem gPlusDown_tangential_tangential
    (C : PENormalMetricComponents Iota)
    (i j : Iota) :
    gPlusDown C (PEIndex.tangential i) (PEIndex.tangential j)
      =
    (C.r ^ 2)⁻¹ * C.h i j := rfl

@[simp]
theorem gPlusUp_radial_radial (C : PENormalMetricComponents Iota) :
    gPlusUp C PEIndex.radial PEIndex.radial = C.r ^ 2 := rfl

@[simp]
theorem gPlusUp_tangential_tangential
    (C : PENormalMetricComponents Iota)
    (i j : Iota) :
    gPlusUp C (PEIndex.tangential i) (PEIndex.tangential j)
      =
    C.r ^ 2 * C.hInv i j := rfl

/-- Left-inverse condition for the boundary metric block. -/
def BoundaryLeftInverse
    [Fintype Iota]
    [DecidableEq Iota]
    (C : PENormalMetricComponents Iota) : Prop :=
  forall i j : Iota,
    (∑ k : Iota, C.hInv i k * C.h k j)
      =
    if i = j then 1 else 0

/--
The displayed contravariant components are a left inverse of the Poincare
metric components.
-/
theorem gPlusUp_mul_gPlusDown
    [Fintype Iota]
    [DecidableEq Iota]
    (C : PENormalMetricComponents Iota)
    (hr : C.r ≠ 0)
    (hbase : BoundaryLeftInverse C)
    (I J : PEIndex Iota) :
    (∑ K : PEIndex Iota, gPlusUp C I K * gPlusDown C K J)
      =
    PEIndex.kronecker I J := by
  classical
  cases I with
  | radial =>
      cases J with
      | radial =>
          rw [PEIndex.sum_index]
          simp [gPlusUp, gPlusDown, PEIndex.kronecker, pow_ne_zero 2 hr]
      | tangential j =>
          rw [PEIndex.sum_index]
          simp [gPlusUp, gPlusDown, PEIndex.kronecker]
  | tangential i =>
      cases J with
      | radial =>
          rw [PEIndex.sum_index]
          simp [gPlusUp, gPlusDown, PEIndex.kronecker]
      | tangential j =>
          rw [PEIndex.sum_index]
          simp only [gPlusUp, gPlusDown, zero_mul, zero_add]
          have hterm :
              forall k : Iota,
                (C.r ^ 2 * C.hInv i k) * ((C.r ^ 2)⁻¹ * C.h k j)
                  =
                C.hInv i k * C.h k j := by
            intro k
            field_simp [pow_ne_zero 2 hr]
          calc
            (∑ k : Iota,
                (C.r ^ 2 * C.hInv i k) * ((C.r ^ 2)⁻¹ * C.h k j))
                =
              ∑ k : Iota, C.hInv i k * C.h k j := by
                apply Finset.sum_congr rfl
                intro k _hk
                exact hterm k
            _ = PEIndex.kronecker
                  (PEIndex.tangential i) (PEIndex.tangential j) := by
                rw [hbase i j]
                by_cases hij : i = j
                · simp [PEIndex.kronecker, hij]
                · simp [PEIndex.kronecker, hij]

end PE
end Ambient
end ConformalStructure
