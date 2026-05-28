import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.Basic

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
# Boundary equivalence for rank-r inputs

The rank-r relations are pointwise lifts of the unary boundary equivalence
relations from `Ambienttangential.lean`.
-/

/-- Pointwise boundary equivalence for rank-r input tuples. -/
def SameBoundaryValues
    {r : ℕ}
    (F G : CalConf.MultiInput r) : Prop :=
  ∀ i : Fin r, CalConf.SameBoundaryValue (F i) (G i)

/-- Weighted pointwise boundary equivalence for rank-r input tuples. -/
def SameBoundaryValueAtWeights
    {r : ℕ}
    (w : Fin r → ℝ)
    (F G : CalConf.MultiInput r) : Prop :=
  ∀ i : Fin r, CalConf.SameBoundaryValueAtWeight (w i) (F i) (G i)

theorem SameBoundaryValues_refl
    {r : ℕ}
    (F : CalConf.MultiInput r) :
    CalConf.SameBoundaryValues F F := by
  intro i
  exact CalConf.SameBoundaryValue_refl (F i)

theorem SameBoundaryValues_symm
    {r : ℕ}
    {F G : CalConf.MultiInput r}
    (hFG : CalConf.SameBoundaryValues F G) :
    CalConf.SameBoundaryValues G F := by
  intro i
  exact CalConf.SameBoundaryValue_symm (hFG i)

theorem SameBoundaryValues_trans
    {r : ℕ}
    {F G K : CalConf.MultiInput r}
    (hFG : CalConf.SameBoundaryValues F G)
    (hGK : CalConf.SameBoundaryValues G K) :
    CalConf.SameBoundaryValues F K := by
  intro i
  exact CalConf.SameBoundaryValue_trans (hFG i) (hGK i)

theorem SameBoundaryValueAtWeights.sameBoundaryValues
    {r : ℕ}
    {w : Fin r → ℝ}
    {F G : CalConf.MultiInput r}
    (hFG : CalConf.SameBoundaryValueAtWeights w F G) :
    CalConf.SameBoundaryValues F G := by
  intro i
  exact SameBoundaryValueAtWeight.sameBoundaryValue (CalConf := CalConf) (hFG i)

end Calculus
end Operators
end Ambient
end ConformalStructure
