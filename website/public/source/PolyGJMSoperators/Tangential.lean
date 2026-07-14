import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.Operators

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
# Tangential rank-r ambient operators
-/

/--
Rank-r tangentiality at a multiweight.

Each input slot carries its own weight and its own weighted boundary
equivalence relation.
-/
def IsTangentialAtWeights
    {r : ℕ}
    (P : CalConf.MultiOperator r)
    (w : Fin r → ℝ) : Prop :=
  ∀ {F G : CalConf.MultiInput r},
    CalConf.IsMultiHomogeneous w F →
    CalConf.IsMultiHomogeneous w G →
    CalConf.SameBoundaryValueAtWeights w F G →
      CalConf.SameBoundaryValue (P F) (P G)

/-- A rank-r operator maps a multiweight to an output weight. -/
def MapsWeights
    {r : ℕ}
    (P : CalConf.MultiOperator r)
    (w : Fin r → ℝ)
    (wout : ℝ) : Prop :=
  ∀ {F : CalConf.MultiInput r},
    CalConf.IsMultiHomogeneous w F →
      CalConf.IsXHomogeneous wout (P F)

/-- A weighted rank-r tangential ambient operator. -/
structure WeightedMultiTangentialOperator
    (r : ℕ) where
  inputWeights : Fin r → ℝ
  outputWeight : ℝ
  toOperator : CalConf.MultiOperator r
  mapsWeights :
    CalConf.MapsWeights toOperator inputWeights outputWeight
  tangential :
    CalConf.IsTangentialAtWeights toOperator inputWeights

/-- Weighted bidifferential ambient operators. -/
abbrev WeightedBiTangentialOperator : Type _ :=
  CalConf.WeightedMultiTangentialOperator 2

/-- Weighted tridifferential ambient operators. -/
abbrev WeightedTriTangentialOperator : Type _ :=
  CalConf.WeightedMultiTangentialOperator 3

namespace IsTangentialAtWeights

variable {CalConf}

theorem add
    {r : ℕ}
    {P Q : CalConf.MultiOperator r}
    {w : Fin r → ℝ}
    (hP : CalConf.IsTangentialAtWeights P w)
    (hQ : CalConf.IsTangentialAtWeights Q w) :
    CalConf.IsTangentialAtWeights (CalConf.multiAdd P Q) w := by
  intro F G hF hG hFG
  exact CalConf.SameBoundaryValue_add (hP hF hG hFG) (hQ hF hG hFG)

theorem smul
    {r : ℕ}
    {P : CalConf.MultiOperator r}
    {w : Fin r → ℝ}
    (c : ℝ)
    (hP : CalConf.IsTangentialAtWeights P w) :
    CalConf.IsTangentialAtWeights (CalConf.multiSmul c P) w := by
  intro F G hF hG hFG
  exact CalConf.SameBoundaryValue_smul c (hP hF hG hFG)

end IsTangentialAtWeights

namespace WeightedMultiTangentialOperator

variable {CalConf}

/--
Add weighted tangential operators with the same input and output weights.

The output homogeneity proof is supplied explicitly; proving it from `X`
linearity belongs to a later algebraic layer.
-/
def add
    {r : ℕ}
    (P Q : CalConf.WeightedMultiTangentialOperator r)
    (hinput : P.inputWeights = Q.inputWeights)
    (_houtput : P.outputWeight = Q.outputWeight)
    (hmaps :
      CalConf.MapsWeights
        (CalConf.multiAdd P.toOperator Q.toOperator)
        P.inputWeights
        P.outputWeight) :
    CalConf.WeightedMultiTangentialOperator r where
  inputWeights := P.inputWeights
  outputWeight := P.outputWeight
  toOperator := CalConf.multiAdd P.toOperator Q.toOperator
  mapsWeights := hmaps
  tangential := by
    intro F G hF hG hFG
    have hFQ :
        CalConf.IsMultiHomogeneous Q.inputWeights F := by
      simpa [hinput] using hF
    have hGQ :
        CalConf.IsMultiHomogeneous Q.inputWeights G := by
      simpa [hinput] using hG
    have hFGQ :
        CalConf.SameBoundaryValueAtWeights Q.inputWeights F G := by
      simpa [hinput] using hFG
    exact
      CalConf.SameBoundaryValue_add
        (P.tangential hF hG hFG)
        (Q.tangential hFQ hGQ hFGQ)

/--
Scalar multiples of weighted tangential operators.

The output homogeneity proof is supplied explicitly; proving it from `X`
linearity belongs to a later algebraic layer.
-/
def smul
    {r : ℕ}
    (c : ℝ)
    (P : CalConf.WeightedMultiTangentialOperator r)
    (hmaps :
      CalConf.MapsWeights
        (CalConf.multiSmul c P.toOperator)
        P.inputWeights
        P.outputWeight) :
    CalConf.WeightedMultiTangentialOperator r where
  inputWeights := P.inputWeights
  outputWeight := P.outputWeight
  toOperator := CalConf.multiSmul c P.toOperator
  mapsWeights := hmaps
  tangential := IsTangentialAtWeights.smul c P.tangential

end WeightedMultiTangentialOperator

end Calculus
end Operators
end Ambient
end ConformalStructure
