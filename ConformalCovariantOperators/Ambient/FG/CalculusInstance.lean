import ConformalCovariantOperators.Ambient.FG.Commutators

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
# From Fefferman-Graham normal form to the existing ambient calculus

This file is the first bridge from the normal-form ambient metric layer to the
operator layer already used by tangentiality, GJMS, poly-GJMS, and Juhl formula
code.
-/

namespace NormalAmbientData

/-- The ambient calculus induced by a certified normal-form Laplacian model. -/
def toCalculus
    (A : NormalAmbientData Conf)
    (L : NormalLaplacianModel A) :
    Operators.Calculus Conf where
  straight := A.toStraightForm
  baseDim := L.baseDim
  Q := normalQ A
  X := L.X
  laplacian := L.laplacian

@[simp]
theorem toCalculus_Q
    (A : NormalAmbientData Conf)
    (L : NormalLaplacianModel A) :
    (A.toCalculus L).Q = normalQ A := rfl

@[simp]
theorem toCalculus_lap
    (A : NormalAmbientData Conf)
    (L : NormalLaplacianModel A)
    (f : Operators.Function Conf) :
    (A.toCalculus L).lap f = L.laplacian f := rfl

end NormalAmbientData

/--
The certified normal-form Laplacian identities instantiate the algebraic
identity package required by the existing tangentiality proofs.
-/
theorem FG_algebraicIdentities
    (A : NormalAmbientData Conf)
    (L : NormalLaplacianModel A) :
    (A.toCalculus L).AlgebraicIdentities := by
  refine
    { X_Q := ?_
      lap_smul := ?_
      lap_add := ?_
      X_lap_comm := ?_
      lap_Q_comm := ?_
      lap_Qpow_of_XHomogeneous := ?_ }
  · exact L.X_Q
  · intro c f
    exact L.lap_smul c f
  · intro f g
    exact L.lap_add f g
  · intro f
    exact L.X_lap_comm f
  · intro f
    simpa [NormalAmbientData.toCalculus, Operators.Calculus.Qmul,
      Operators.Calculus.n, normalQmul] using L.lap_Q_comm f
  · intro m w f hf
    simpa [NormalAmbientData.toCalculus, Operators.Calculus.QpowMul,
      Operators.Calculus.IsXHomogeneous, Operators.Calculus.n,
      normalQpowMul] using L.lap_Qpow_of_XHomogeneous m hf

/-- Alias matching the first-stage target name. -/
theorem straightForm_instantiates_AlgebraicIdentities
    (A : NormalAmbientData Conf)
    (L : NormalLaplacianModel A) :
    (A.toCalculus L).AlgebraicIdentities :=
  FG_algebraicIdentities A L

end FG
end Ambient
end ConformalStructure
