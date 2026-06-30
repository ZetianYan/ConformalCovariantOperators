import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.TreeLaplacianWords

open Classical
open scoped BigOperators

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus

variable {M : Type u}
variable {Conf : ConformalStructure.{u, v} M}

/-!
# Path-wise recurrence for left-comb tree words

This file formalizes the rank-general recurrence controlling the slot-wise
`Q`-commutator defects for left-comb nested Laplacian words.

It does not prove the commutator formula.  It records the finite combinatorial
objects that the commutator formula should produce.
-/

/-- Coefficient space of total tree degree `k`. -/
abbrev CombCoeffSpace (r k : ℕ) : Type :=
  CombIndex r k → ℝ

namespace LeftComb

/-- Vertex corresponding to the `j`-th leaf. -/
def leafVertex {r : ℕ} (j : Fin r) : Fin (leftCombVertexCount r) :=
  ⟨(r - 1) + j.val, by
    have hj := j.isLt
    unfold leftCombVertexCount
    omega⟩

/-- A vertex is internal in the left-comb layout. -/
def IsInternal {r : ℕ} (v : Fin (leftCombVertexCount r)) : Prop :=
  v.val < r - 1

/-- A leaf lies below a given vertex. -/
def leafBelow {r : ℕ}
    (v : Fin (leftCombVertexCount r))
    (j : Fin r) : Prop :=
  if _hv : IsInternal (r := r) v then
    j.val < r - v.val
  else
    v = leafVertex j

/-- A vertex lies on the path from leaf `j` to the root. -/
def onPathToRoot {r : ℕ}
    (j : Fin r)
    (v : Fin (leftCombVertexCount r)) : Prop :=
  v = leafVertex j ∨
    (IsInternal (r := r) v ∧ v.val < r - j.val)

/-- The path from leaf `j` to the root, including the leaf and root. -/
def pathToRoot {r : ℕ}
    (j : Fin r) : Finset (Fin (leftCombVertexCount r)) :=
  Finset.univ.filter fun v => onPathToRoot j v

/-- `x` is a proper descendant of `v` in the left-comb tree. -/
def isDescendant {r : ℕ}
    (v x : Fin (leftCombVertexCount r)) : Prop :=
  IsInternal (r := r) v ∧
    ((x.val < r - 1 ∧ v.val < x.val) ∨
      (r - 1 ≤ x.val ∧ x.val < 2 * r - v.val - 1))

/-- Proper descendants of a vertex. -/
def descendants {r : ℕ}
    (v : Fin (leftCombVertexCount r)) :
    Finset (Fin (leftCombVertexCount r)) :=
  Finset.univ.filter fun x => isDescendant v x

/-- Sum of the input weights under the subtree rooted at `v`. -/
def subtreeWeight {r : ℕ}
    (v : Fin (leftCombVertexCount r))
    (w : Fin r → ℝ) : ℝ :=
  (Finset.univ.filter fun j : Fin r => leafBelow v j).sum fun j => w j

/-- Sum of the powers on the proper descendants of `v`. -/
def descendantPowerSum {r s : ℕ}
    (β : CombIndex r s)
    (v : Fin (leftCombVertexCount r)) : ℕ :=
  (descendants v).sum fun x => β.power x

/-- The single-vertex defect coefficient `C_v(β)`.

Mathematically this is

`n / 2 + W_v - 2 * sum_{x in Desc(v)} β_x - β_v - 1`.
-/
def defectCoeff {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (β : CombIndex r s)
    (v : Fin (leftCombVertexCount r)) : ℝ :=
  n / 2 + subtreeWeight v w
    - 2 * (descendantPowerSum β v : ℝ)
    - (β.power v : ℝ)
    - 1

/-- The contribution of one vertex to a lowering recurrence operator. -/
def lowerAtVertex {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (v : Fin (leftCombVertexCount r))
    (A : CombCoeffSpace r (s + 1)) :
    CombCoeffSpace r s :=
  fun β => defectCoeff n w β v * A (β.addAt v)

/-- The defect coefficient `B_j(β)` for the `j`-th input slot. -/
def pathDefectCoeff {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (A : CombCoeffSpace r (s + 1))
    (j : Fin r)
    (β : CombIndex r s) : ℝ :=
  (pathToRoot j).sum fun v =>
    defectCoeff n w β v * A (β.addAt v)

/-- The first differential `d_1 A = (R_1 A, ..., R_r A)`. -/
def dOne {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (A : CombCoeffSpace r (s + 1)) :
    Fin r → CombCoeffSpace r s :=
  fun j β => pathDefectCoeff n w A j β

/-- Slot-wise recurrence at level `s+1`. -/
def RankRecurrenceAtLevel {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (A : CombCoeffSpace r (s + 1)) : Prop :=
  ∀ (j : Fin r) (β : CombIndex r s),
    pathDefectCoeff n w A j β = 0

/-- Rank recurrence for a coefficient system of total degree `k`.

At `k = 0` there is no lowering recurrence.
-/
def RankRecurrence {r k : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
  (A : CombCoeffSpace r k) : Prop :=
  match k with
  | 0 => True
  | _s + 1 => RankRecurrenceAtLevel n w A

theorem recurrence_iff_dOne_zero {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (A : CombCoeffSpace r (s + 1)) :
    RankRecurrenceAtLevel n w A
      ↔
    dOne n w A = fun _j => (fun _β => 0) := by
  constructor
  · intro h
    funext j β
    exact h j β
  · intro h j β
    exact congrFun (congrFun h j) β

end LeftComb

end Calculus
end Operators
end Ambient
end ConformalStructure
