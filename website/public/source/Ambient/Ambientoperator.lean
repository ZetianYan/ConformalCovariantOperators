import Mathlib
import ConformalCovariantOperators.Ambient.Ambientbasic
import ConformalCovariantOperators.Ambient.Ambientdensity


open Classical

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace Operators

variable {M : Type u}
variable (Conf : ConformalStructure.{u, v} M)

/-!
# Ambient operators

This file is built on the already existing ambient bundle and ambient density
definitions.

We do not redefine:

* `Conf.AmbientBundle`;
* `Ambient.Equivariant.Density`.

Instead, we add a formal calculus package containing the three ambient
quantities needed for the later algebraic identities:

* `Q`;
* `X`;
* `laplacian`.

The algebraic identities among `Q`, `X`, and `laplacian` are recorded as fields.
-/


/-! ## Ambient scalar functions -/

/-- Real-valued functions on the ambient bundle. -/
abbrev Function : Type _ :=
  Conf.AmbientBundle → ℝ


/-! ## Pointwise operations -/

/-- Pointwise zero function. -/
def zero : Function Conf :=
  fun _ => 0

/-- Pointwise addition. -/
def add (f g : Function Conf) : Function Conf :=
  fun U => f U + g U

/-- Pointwise subtraction. -/
def sub (f g : Function Conf) : Function Conf :=
  fun U => f U - g U

/-- Pointwise multiplication. -/
def mul (f g : Function Conf) : Function Conf :=
  fun U => f U * g U

/-- Scalar multiplication of an ambient function. -/
def smul (c : ℝ) (f : Function Conf) : Function Conf :=
  fun U => c * f U

/-- Pointwise natural power. -/
def pow (f : Function Conf) (m : ℕ) : Function Conf :=
  fun U => f U ^ m


/-! ## Ambient calculus data -/

/--
Formal ambient calculus data attached to the existing ambient bundle.

The field `straight` records that this calculus is being used in straight
ambient form.

The fields `Q`, `X`, and `laplacian` are the three quantities entering the
ambient algebraic identities.
-/
structure Calculus where
  /-- The straight-form ambient metric data already defined in `Ambientbasic`. -/
  straight : Conf.StraightForm

  /-- The formal base dimension `n`. -/
  baseDim : ℝ

  /-- The defining function `Q = |X|²`. -/
  Q : Function Conf

  /-- The infinitesimal dilation operator. -/
  X : Function Conf → Function Conf

  /-- The ambient Laplacian `Δ̃`. -/
  laplacian : Function Conf → Function Conf

namespace Calculus

variable {Conf : ConformalStructure.{u, v} M}
variable (CalConf : Calculus Conf)


/-! ## Basic derived operators -/

/-- The formal dimension parameter. -/
def n : ℝ :=
  CalConf.baseDim

/-- Multiplication by `Q`. -/
def Qmul (f : Function Conf) : Function Conf :=
  fun U => CalConf.Q U * f U

/-- Multiplication by `Q^m`. -/
def QpowMul (m : ℕ) (f : Function Conf) : Function Conf :=
  fun U => CalConf.Q U ^ m * f U

/-- A function vanishes modulo `Q` if it is divisible by `Q`. -/
def VanishesModQ (f : Function Conf) : Prop :=
  ∃ h : Function Conf, f = CalConf.Qmul h

/-- Equality modulo `Q`. -/
def EqModQ (f g : Function Conf) : Prop :=
  CalConf.VanishesModQ (fun U => f U - g U)

@[refl]
theorem EqModQ_refl (f : Function Conf) :
    CalConf.EqModQ f f := by
  unfold EqModQ VanishesModQ Qmul
  refine ⟨fun _ => 0, ?_⟩
  funext U
  simp

/-- The ambient Laplacian. -/
def lap (f : Function Conf) : Function Conf :=
  CalConf.laplacian f

/--
Iterated ambient Laplacian.

This definition deliberately uses `Nat.rec` instead of recursive notation
through namespace projections. It is more stable in Lean.

`CalConf.lapPow r f` means `Δ̃^r f`.
-/
def lapPow (r : ℕ) (f : Function Conf) : Function Conf :=
  Nat.rec f
    (fun _ g => CalConf.lap g)
    r

@[simp]
theorem lapPow_zero (f : Function Conf) :
    CalConf.lapPow 0 f = f := rfl

@[simp]
theorem lapPow_succ (r : ℕ) (f : Function Conf) :
    CalConf.lapPow (r + 1) f =
      CalConf.lap (CalConf.lapPow r f) := rfl


/-! ## Homogeneity with respect to `X` -/

/--
Infinitesimal homogeneity of weight `w`.

This is the formal version of

`X f = w f`.
-/
def IsXHomogeneous (w : ℝ) (f : Function Conf) : Prop :=
  CalConf.X f = fun U => w * f U

/--
The already existing ambient density can be checked against infinitesimal
homogeneity using `X`.

Important: this is only for real-valued ambient densities, because `X` acts on
real-valued ambient functions.
-/
def IsXHomogeneousDensity
    {χ : Weight ℝ}
    (w : ℝ)
    (d : Ambient.Equivariant.Density (Conf := Conf) χ) : Prop :=
  CalConf.IsXHomogeneous w d.toFun

/-- The underlying real-valued ambient function of an existing ambient density. -/
def densityToFunction
    (_CalConf : Calculus Conf)
    {χ : Weight ℝ}
    (d : Ambient.Equivariant.Density (Conf := Conf) χ) :
    Function Conf :=
  d.toFun

@[simp]
theorem densityToFunction_apply
    {χ : Weight ℝ}
    (d : Ambient.Equivariant.Density (Conf := Conf) χ)
    (U : Conf.AmbientBundle) :
    CalConf.densityToFunction d U = d U := rfl

theorem IsXHomogeneousDensity_iff
    {χ : Weight ℝ}
    (w : ℝ)
    (d : Ambient.Equivariant.Density (Conf := Conf) χ) :
    CalConf.IsXHomogeneousDensity w d
      ↔
    CalConf.IsXHomogeneous w d.toFun := by
  rfl


/-! ## Algebraic identities for `Q`, `X`, and `Δ̃` -/

/--
The formal algebraic identities among `Q`, `X`, and the ambient Laplacian.

These are recorded as hypotheses at the current abstraction level.

Later, after a genuine ambient metric, connection, and Laplacian are available,
these fields can be replaced by actual theorems.
-/
structure AlgebraicIdentities : Prop where
  /-- `Q` is homogeneous of weight `2`. -/
  X_Q :
    CalConf.X CalConf.Q = fun U => 2 * CalConf.Q U

  /--
  Linearity of the ambient Laplacian with respect to constant scalar
  multiplication.
  -/
  lap_smul :
    ∀ (c : ℝ) (f : Function Conf),
      CalConf.lap (fun U => c * f U)
        =
      fun U => c * CalConf.lap f U

  /--
  Additivity of the ambient Laplacian.
  -/
  lap_add :
    ∀ f g : Function Conf,
      CalConf.lap (fun U => f U + g U)
        =
      fun U => CalConf.lap f U + CalConf.lap g U

  /--
  The Laplacian lowers homogeneity by two.

  Written as

  `X (Δ̃ f) = Δ̃ (X f) - 2 Δ̃ f`.
  -/
  X_lap_comm :
    ∀ f : Function Conf,
      CalConf.X (CalConf.lap f)
        =
      fun U => CalConf.lap (CalConf.X f) U - 2 * CalConf.lap f U

  /--
  The basic commutator between `Δ̃` and `Q`.

  This records the formal identity

  `[Δ̃, Q] = 2(2X + n + 2)`.
  -/
  lap_Q_comm :
    ∀ f : Function Conf,
      CalConf.lap (CalConf.Qmul f)
        =
      fun U =>
        CalConf.Q U * CalConf.lap f U
          + 2 * (2 * CalConf.X f U + (CalConf.n + 2) * f U)

  /--
  The homogeneous `Q^m` formula.

  If `X f = w f`, then

  `Δ̃(Q^m f)
   = Q^m Δ̃f + 2m(2w + n + 2m) Q^(m-1) f`.

  This is kept as a field for now because it is exactly the form needed later
  in the tangentiality calculation.
  -/
  lap_Qpow_of_XHomogeneous :
    ∀ (m : ℕ) {w : ℝ} {f : Function Conf},
      CalConf.IsXHomogeneous w f →
        CalConf.lap (CalConf.QpowMul m f)
          =
        fun U =>
          CalConf.Q U ^ m * CalConf.lap f U
            + 2 * (m : ℝ)
              * (2 * w + CalConf.n + 2 * (m : ℝ))
              * CalConf.Q U ^ (m - 1)
              * f U
theorem lap_smul
    (H : CalConf.AlgebraicIdentities)
    (c : ℝ)
    (f : Function Conf) :
    CalConf.lap (fun U => c * f U)
      =
    fun U => c * CalConf.lap f U := by
  exact H.lap_smul c f

theorem lap_add
    (H : CalConf.AlgebraicIdentities)
    (f g : Function Conf) :
    CalConf.lap (fun U => f U + g U)
      =
    fun U => CalConf.lap f U + CalConf.lap g U := by
  exact H.lap_add f g



theorem X_Q
    (H : CalConf.AlgebraicIdentities) :
    CalConf.X CalConf.Q = fun U => 2 * CalConf.Q U := by
  exact H.X_Q

theorem X_lap_comm
    (H : CalConf.AlgebraicIdentities)
    (f : Function Conf) :
    CalConf.X (CalConf.lap f)
      =
    fun U => CalConf.lap (CalConf.X f) U - 2 * CalConf.lap f U := by
  exact H.X_lap_comm f

theorem lap_Q_comm
    (H : CalConf.AlgebraicIdentities)
    (f : Function Conf) :
    CalConf.lap (CalConf.Qmul f)
      =
    fun U =>
      CalConf.Q U * CalConf.lap f U
        + 2 * (2 * CalConf.X f U + (CalConf.n + 2) * f U) := by
  exact H.lap_Q_comm f

theorem lap_Qpow_of_XHomogeneous
    (H : CalConf.AlgebraicIdentities)
    (m : ℕ)
    {w : ℝ}
    {f : Function Conf}
    (hf : CalConf.IsXHomogeneous w f) :
    CalConf.lap (CalConf.QpowMul m f)
      =
    fun U =>
      CalConf.Q U ^ m * CalConf.lap f U
        + 2 * (m : ℝ)
          * (2 * w + CalConf.n + 2 * (m : ℝ))
          * CalConf.Q U ^ (m - 1)
          * f U := by
  exact H.lap_Qpow_of_XHomogeneous m hf

theorem lap_sub
    (H : CalConf.AlgebraicIdentities)
    (f g : Function Conf) :
    CalConf.lap (fun U => f U - g U)
      =
    fun U => CalConf.lap f U - CalConf.lap g U := by
  have hsub :
      (fun U => f U - g U)
        =
      fun U => f U + (-1 : ℝ) * g U := by
    funext U
    ring
  rw [hsub, CalConf.lap_add H f (fun U => (-1 : ℝ) * g U)]
  rw [CalConf.lap_smul H (-1) g]
  funext U
  ring

theorem lapPow_sub
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    (f g : Function Conf) :
    CalConf.lapPow k (fun U => f U - g U)
      =
    fun U => CalConf.lapPow k f U - CalConf.lapPow k g U := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [CalConf.lapPow_succ k (fun U => f U - g U), ih]
      rw [CalConf.lap_sub H (CalConf.lapPow k f) (CalConf.lapPow k g)]
      rw [CalConf.lapPow_succ k f, CalConf.lapPow_succ k g]

/-! ## Consequences for weight bookkeeping -/

/--
If `f` is homogeneous of weight `w`, then `Δ̃ f` is homogeneous of weight
`w - 2`.

This follows from the commutator relation between `X` and `Δ̃`.
-/
theorem lap_isXHomogeneous
    (H : CalConf.AlgebraicIdentities)
    {w : ℝ}
    {f : Function Conf}
    (hf : CalConf.IsXHomogeneous w f) :
    CalConf.IsXHomogeneous (w - 2) (CalConf.lap f) := by
  unfold IsXHomogeneous at hf ⊢
  rw [CalConf.X_lap_comm H f, hf]
  rw [CalConf.lap_smul H w f]
  funext U
  ring_nf

/--
Predicate saying that `Δ̃^r f` has weight `w - 2r`.
-/
def LapPowHasWeight
    (r : ℕ)
    (w : ℝ)
    (f : Function Conf) : Prop :=
  CalConf.IsXHomogeneous (w - 2 * (r : ℝ)) (CalConf.lapPow r f)

/--
Weight bookkeeping for iterated ambient Laplacians.

If `X f = w f`, then

`X (Δ̃^r f) = (w - 2r) Δ̃^r f`.
-/
theorem lapPow_isXHomogeneous
    (H : CalConf.AlgebraicIdentities)
    (r : ℕ)
    {w : ℝ}
    {f : Function Conf}
    (hf : CalConf.IsXHomogeneous w f) :
    CalConf.LapPowHasWeight r w f := by
  induction r with
  | zero =>
      unfold LapPowHasWeight
      simpa [lapPow] using hf
  | succ r ih =>
      have ih' :
          CalConf.IsXHomogeneous
            (w - 2 * (r : ℝ))
            (CalConf.lapPow r f) := by
        simpa [LapPowHasWeight] using ih

      have hstep :
          CalConf.IsXHomogeneous
            ((w - 2 * (r : ℝ)) - 2)
            (CalConf.lap (CalConf.lapPow r f)) :=
        CalConf.lap_isXHomogeneous H ih'

      have hweight :
          ((w - 2 * (r : ℝ)) - 2)
            =
          w - 2 * ((r + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring_nf

      unfold LapPowHasWeight
      simpa [lapPow, hweight] using hstep

/--
Iterated commutator formula for powers of the ambient Laplacian applied to a
single `Q`-multiple.
-/
theorem lapPow_Qmul_formula
    (H : CalConf.AlgebraicIdentities)
    (k : ℕ)
    {w : ℝ}
    {h : Function Conf}
    (hh : CalConf.IsXHomogeneous w h) :
    CalConf.lapPow k (CalConf.Qmul h)
      =
    fun U =>
      CalConf.Q U * CalConf.lapPow k h U
        +
      2 * (k : ℝ)
        * (2 * w + CalConf.n + 2 - 2 * (((k - 1 : ℕ) : ℝ)))
        * CalConf.lapPow (k - 1) h U := by
  induction k with
  | zero =>
      funext U
      simp [lapPow, Qmul]
  | succ k ih =>
      cases k with
      | zero =>
          rw [CalConf.lapPow_succ 0 (CalConf.Qmul h)]
          change CalConf.lap (CalConf.Qmul h) = _
          rw [CalConf.lap_Q_comm H h]
          unfold IsXHomogeneous at hh
          rw [hh]
          funext U
          simp [lapPow]
          ring
      | succ r =>
          have hhom :
              CalConf.IsXHomogeneous
                (w - 2 * ((r + 1 : ℕ) : ℝ))
                (CalConf.lapPow (r + 1) h) := by
            simpa [LapPowHasWeight] using
              CalConf.lapPow_isXHomogeneous H (r + 1) hh
          unfold IsXHomogeneous at hhom

          rw [CalConf.lapPow_succ (r + 1) (CalConf.Qmul h)]
          rw [ih]

          change
            CalConf.lap
              (fun U =>
                (CalConf.Qmul (CalConf.lapPow (r + 1) h)) U
                  +
                2 * (((r + 1 : ℕ) : ℝ))
                  * (2 * w + CalConf.n + 2 - 2 * (((r + 1 - 1 : ℕ) : ℝ)))
                  * CalConf.lapPow (r + 1 - 1) h U)
              =
            fun U =>
              CalConf.Q U * CalConf.lapPow (r + 1 + 1) h U
                +
              2 * (((r + 1 + 1 : ℕ) : ℝ))
                * (2 * w + CalConf.n + 2 - 2 * (((r + 1 + 1 - 1 : ℕ) : ℝ)))
                * CalConf.lapPow (r + 1 + 1 - 1) h U

          rw [CalConf.lap_add H
            (CalConf.Qmul (CalConf.lapPow (r + 1) h))
            (fun U =>
              2 * (((r + 1 : ℕ) : ℝ))
                * (2 * w + CalConf.n + 2 - 2 * (((r + 1 - 1 : ℕ) : ℝ)))
                * CalConf.lapPow (r + 1 - 1) h U)]
          rw [CalConf.lap_Q_comm H (CalConf.lapPow (r + 1) h)]
          rw [CalConf.lap_smul H
            (2 * (((r + 1 : ℕ) : ℝ))
              * (2 * w + CalConf.n + 2 - 2 * (((r + 1 - 1 : ℕ) : ℝ))))
            (CalConf.lapPow (r + 1 - 1) h)]
          rw [hhom]
          funext U
          simp [lapPow, Nat.cast_add, Nat.cast_one]
          ring

end Calculus

end Operators
end Ambient
end ConformalStructure
