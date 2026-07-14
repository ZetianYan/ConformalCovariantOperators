import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.Boundary

open Classical
open BigOperators

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
# Multiweight homogeneity

Input weights for a rank-r operator are functions `Fin r → ℝ`.
-/

/-- Pointwise homogeneity for rank-r input tuples. -/
def IsMultiHomogeneous
    {r : ℕ}
    (w : Fin r → ℝ)
    (F : CalConf.MultiInput r) : Prop :=
  ∀ i : Fin r, CalConf.IsXHomogeneous (w i) (F i)

/-- Total input weight. -/
def totalWeight
    (_CalConf : Calculus Conf)
    {r : ℕ}
    (w : Fin r → ℝ) : ℝ :=
  ∑ i, w i

/-- Expected output weight after lowering total degree by `2N`. -/
def outputWeight
    (CalConf : Calculus Conf)
    {r : ℕ}
    (w : Fin r → ℝ)
    (N : ℕ) : ℝ :=
  CalConf.totalWeight w - 2 * (N : ℝ)

theorem IsMultiHomogeneous.apply
    {r : ℕ}
    {w : Fin r → ℝ}
    {F : CalConf.MultiInput r}
    (hF : CalConf.IsMultiHomogeneous w F)
    (i : Fin r) :
    CalConf.IsXHomogeneous (w i) (F i) :=
  hF i

theorem totalWeight_fin_two
    (w : Fin 2 → ℝ) :
    CalConf.totalWeight w = w 0 + w 1 := by
  unfold totalWeight
  rw [Fin.sum_univ_two]

theorem totalWeight_fin_three
    (w : Fin 3 → ℝ) :
    CalConf.totalWeight w = w 0 + w 1 + w 2 := by
  unfold totalWeight
  rw [Fin.sum_univ_three]

@[simp]
theorem outputWeight_def
    {r : ℕ}
    (w : Fin r → ℝ)
    (N : ℕ) :
    CalConf.outputWeight w N =
      CalConf.totalWeight w - 2 * (N : ℝ) := by
  rfl

end Calculus
end Operators
end Ambient
end ConformalStructure
