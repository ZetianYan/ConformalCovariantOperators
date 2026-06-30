import ConformalCovariantOperators.Ambient.FG.Laplacian

open Classical
open scoped BigOperators

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace FG

variable {M : Type u}
variable {Conf : ConformalStructure.{u, v} M}
variable {A : NormalAmbientData Conf}

/-!
# Normal-form commutator identities

These theorems expose the certified normal-form identities with names matching
the Fefferman-Graham calculations.  The final bridge to the existing calculus
is in `CalculusInstance.lean`.
-/

theorem straightForm_X_Q
    (L : NormalLaplacianModel A) :
    L.X (normalQ A) = fun U => 2 * normalQ A U :=
  L.X_Q

theorem straightForm_X_laplacian_comm
    (L : NormalLaplacianModel A)
    (f : Operators.Function Conf) :
    L.X (L.laplacian f)
      =
    fun U => L.laplacian (L.X f) U - 2 * L.laplacian f U :=
  L.X_lap_comm f

theorem straightForm_lap_Q_comm
    (L : NormalLaplacianModel A)
    (f : Operators.Function Conf) :
    L.laplacian (normalQmul A f)
      =
    fun U =>
      normalQ A U * L.laplacian f U
        + 2 * (2 * L.X f U + (L.baseDim + 2) * f U) :=
  L.lap_Q_comm f

theorem straightForm_lap_Qpow_of_XHomogeneous
    (L : NormalLaplacianModel A)
    (m : ℕ)
    {w : ℝ}
    {f : Operators.Function Conf}
    (hf : L.X f = fun U => w * f U) :
    L.laplacian (normalQpowMul A m f)
      =
    fun U =>
      normalQ A U ^ m * L.laplacian f U
        + 2 * (m : ℝ)
          * (2 * w + L.baseDim + 2 * (m : ℝ))
          * normalQ A U ^ (m - 1)
          * f U :=
  L.lap_Qpow_of_XHomogeneous m hf

end FG
end Ambient
end ConformalStructure
