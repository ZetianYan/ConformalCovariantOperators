import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.LaplacianWords

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
variable (CalConf : Calculus Conf)

/-!
# Nested left-comb Laplacian words

This file introduces the first rank-general syntax for the Case--Cieslak
type nested multilinear Laplacian words.

For now we use the left-comb tree.  For `r = 3` this is the word

`Delta^a0 (Delta^a1 ((Delta^a2 u0) * (Delta^a3 u1)) * Delta^a4 u2)`.

Thus a rank-`r` word has `2 * r - 1` Laplacian powers, one for each vertex of
the left-comb binary tree.
-/

/-- Number of vertices in a full binary tree with `r` ordered leaves. -/
def leftCombVertexCount (r : ℕ) : ℕ :=
  2 * r - 1

/-- A left-comb tree Laplacian index of total degree `k`. -/
structure CombIndex (r k : ℕ) where
  power : Fin (leftCombVertexCount r) → ℕ
  sum_eq :
    Finset.univ.sum (fun v : Fin (leftCombVertexCount r) => power v) = k
deriving DecidableEq

/-- Rank-general tree index alias.  Later this can be widened from left-combs
to arbitrary rooted binary trees without changing downstream recurrence code
too much.
-/
abbrev PolyTreeIndex := CombIndex

namespace CombIndex

variable {CalConf}

/-- Total Laplacian degree of a comb index. -/
def totalPower {r k : ℕ} (I : CombIndex r k) : ℕ :=
  Finset.univ.sum (fun v : Fin (leftCombVertexCount r) => I.power v)

@[simp]
theorem totalPower_eq {r k : ℕ} (I : CombIndex r k) :
    I.totalPower = k := by
  exact I.sum_eq

/-- Read a vertex power using a natural-number code, returning `0` outside
the vertex range.  This is convenient for recursive word evaluation.
-/
def powerAt {r k : ℕ} (I : CombIndex r k) (i : ℕ) : ℕ :=
  if h : i < leftCombVertexCount r then
    I.power ⟨i, h⟩
  else
    0

@[simp]
theorem powerAt_of_fin {r k : ℕ} (I : CombIndex r k)
    (v : Fin (leftCombVertexCount r)) :
    I.powerAt v.val = I.power v := by
  simp [powerAt, v.isLt]

/-- Add one unit of Laplacian power at a chosen vertex. -/
def addAt {r s : ℕ}
    (I : CombIndex r s)
    (v : Fin (leftCombVertexCount r)) :
    CombIndex r (s + 1) where
  power := Function.update I.power v (I.power v + 1)
  sum_eq := by
    classical
    rw [Finset.sum_update_of_mem
      (s := Finset.univ)
      (i := v)
      (Finset.mem_univ v)
      I.power
      (I.power v + 1)]
    have hsum :
        I.power v + ∑ x ∈ Finset.univ \ {v}, I.power x = s := by
      rw [← Finset.sum_eq_add_sum_diff_singleton
        (s := Finset.univ)
        (i := v)
        (Finset.mem_univ v)
        I.power]
      exact I.sum_eq
    omega

@[simp]
theorem addAt_power_same {r s : ℕ}
    (I : CombIndex r s)
    (v : Fin (leftCombVertexCount r)) :
    (I.addAt v).power v = I.power v + 1 := by
  classical
  simp [addAt]

@[simp]
theorem addAt_power_ne {r s : ℕ}
    (I : CombIndex r s)
    {v x : Fin (leftCombVertexCount r)}
    (hxv : x ≠ v) :
    (I.addAt v).power x = I.power x := by
  classical
  simp [addAt, Function.update, hxv]

/-- Multinomial coefficient attached to a tree index. -/
def multinomialCoeffQ {r k : ℕ} (I : CombIndex r k) : ℚ :=
  (Nat.factorial k : ℚ) /
    (Finset.univ.prod fun v : Fin (leftCombVertexCount r) =>
      (Nat.factorial (I.power v) : ℚ))

end CombIndex

/-- Evaluate a left-comb word using a raw natural-number power function.

The recursive convention is:

* `r = 1`: `Delta^(p 0) u_0`;
* `r + 1`: apply `Delta^(p 0)` to the product of the left `r`-comb using
  shifted powers `p(i+1)` and the final leaf `Delta^(p(2r)) u_r`.
-/
def leftCombEvalFrom
    (CalConf : Calculus Conf) :
    (r : ℕ) → (ℕ → ℕ) → CalConf.MultiInput r → Function Conf
  | 0, _p, _F => zero Conf
  | 1, p, F => CalConf.lapPow (p 0) (F 0)
  | r + 2, p, F =>
      let leftInput : CalConf.MultiInput (r + 1) :=
        fun i => F ⟨i.val, by
          have hi := i.isLt
          omega⟩
      let leftWord : Function Conf :=
        leftCombEvalFrom CalConf (r + 1) (fun i => p (i + 1)) leftInput
      let lastLeaf : Function Conf :=
        CalConf.lapPow (p (2 * (r + 2) - 2))
          (F ⟨r + 1, by omega⟩)
      CalConf.lapPow (p 0) (fun U => leftWord U * lastLeaf U)

namespace CombIndex

/-- The rank-`r` multi-operator represented by a left-comb tree index. -/
def toOperator {r k : ℕ}
    (I : CombIndex r k)
    (CalConf : Calculus Conf) :
    CalConf.MultiOperator r :=
  leftCombEvalFrom CalConf r I.powerAt

@[simp]
theorem toOperator_apply {r k : ℕ}
    (I : CombIndex r k)
    (F : CalConf.MultiInput r) :
    I.toOperator CalConf F =
      leftCombEvalFrom CalConf r I.powerAt F := by
  rfl

end CombIndex

end Calculus
end Operators
end Ambient
end ConformalStructure
