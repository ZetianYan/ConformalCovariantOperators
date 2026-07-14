import ConformalCovariantOperators.Ambient.Ambientoperator
import ConformalCovariantOperators.Ambient.FG.Christoffel

open Classical
open scoped BigOperators

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace FG

variable {M : Type u}
variable {Conf : ConformalStructure.{u, v} M}

/-!
# Normal-form `Q`, dilation, and Laplacian models

The project does not yet contain a full differentiable tensor calculus.  This
file therefore packages the normal-form operators as a certified model: the
operator fields are concrete data, and the normal-form identities they satisfy
are proof obligations.  `CalculusInstance.lean` converts such a model into the
existing `Operators.Calculus.AlgebraicIdentities`.
-/

/-- Convert the positive scale coordinate to a real number. -/
def posRealToReal (a : PosReal) : ℝ :=
  (a.val : ℝ)

/-- The chosen-scale `t` coordinate on the ambient bundle. -/
noncomputable def scaleT
    (s : Conf.Scale)
    (U : Conf.AmbientBundle) : ℝ :=
  posRealToReal ((Conf.trivialization s U.1).1)

/-- The normal-form defining function `Q = |T|^2 = 2 rho t^2`. -/
noncomputable def normalQ
    (A : NormalAmbientData Conf) :
    Operators.Function Conf :=
  fun U => 2 * Conf.rhoCoord U * (scaleT A.baseScale U) ^ 2

@[simp]
theorem normalQ_apply
    (A : NormalAmbientData Conf)
    (U : Conf.AmbientBundle) :
    normalQ A U = 2 * Conf.rhoCoord U * (scaleT A.baseScale U) ^ 2 := rfl

/-- Multiplication by the normal-form defining function `Q`. -/
def normalQmul
    (A : NormalAmbientData Conf)
    (f : Operators.Function Conf) :
    Operators.Function Conf :=
  fun U => normalQ A U * f U

/-- Multiplication by `Q^m` in normal form. -/
def normalQpowMul
    (A : NormalAmbientData Conf)
    (m : ℕ)
    (f : Operators.Function Conf) :
    Operators.Function Conf :=
  fun U => normalQ A U ^ m * f U

/--
A certified normal-form model for the dilation operator and ambient Laplacian.

The fields are deliberately the same identities expected by the existing
ambient calculus layer, but with `Q` fixed to the Fefferman-Graham normal-form
function `2 rho t^2`.
-/
structure NormalLaplacianModel (A : NormalAmbientData Conf) where
  /-- The formal base dimension `n`. -/
  baseDim : ℝ
  /-- Infinitesimal dilation operator `X = t d/dt`. -/
  X : Operators.Function Conf → Operators.Function Conf
  /-- Ambient Laplacian in straight normal form. -/
  laplacian : Operators.Function Conf → Operators.Function Conf
  /-- `Q` is homogeneous of weight `2`. -/
  X_Q :
    X (normalQ A) = fun U => 2 * normalQ A U
  /-- Linearity with respect to constant scalar multiplication. -/
  lap_smul :
    ∀ (c : ℝ) (f : Operators.Function Conf),
      laplacian (fun U => c * f U) = fun U => c * laplacian f U
  /-- Additivity. -/
  lap_add :
    ∀ f g : Operators.Function Conf,
      laplacian (fun U => f U + g U)
        = fun U => laplacian f U + laplacian g U
  /-- The Laplacian lowers `X`-homogeneity by two. -/
  X_lap_comm :
    ∀ f : Operators.Function Conf,
      X (laplacian f)
        =
      fun U => laplacian (X f) U - 2 * laplacian f U
  /-- The basic commutator `[Delta~, Q] = 2(2X+n+2)`. -/
  lap_Q_comm :
    ∀ f : Operators.Function Conf,
      laplacian (normalQmul A f)
        =
      fun U =>
        normalQ A U * laplacian f U
          + 2 * (2 * X f U + (baseDim + 2) * f U)
  /-- The homogeneous `Q^m` formula used by tangentiality. -/
  lap_Qpow_of_XHomogeneous :
    ∀ (m : ℕ) {w : ℝ} {f : Operators.Function Conf},
      X f = (fun U => w * f U) →
        laplacian (normalQpowMul A m f)
          =
        fun U =>
          normalQ A U ^ m * laplacian f U
            + 2 * (m : ℝ)
              * (2 * w + baseDim + 2 * (m : ℝ))
              * normalQ A U ^ (m - 1)
              * f U

/-- The normal-form expression for `Q`. -/
theorem straightForm_Q_eq
    (A : NormalAmbientData Conf) :
    normalQ A = fun U => 2 * Conf.rhoCoord U * (scaleT A.baseScale U) ^ 2 := rfl

end FG
end Ambient
end ConformalStructure
