import Mathlib
import ExtrinsicGJMSOperators.Geometry.PolyGJMSoperators.TreeDefectCancellation

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
# First chain-complex layer for rank-general tree recurrences

This file records the combinatorial first differential and the expected generic
Euler-characteristic dimension for the left-comb recurrence complex.

The higher Koszul-type differentials and generic exactness proof are left for
later files.
-/

namespace LeftComb

/-- Number of degree-`s` tree indices for a left-comb rank-`r` word, as a
stars-and-bars expression.
-/
def combIndexCard (r s : ℕ) : ℕ :=
  Nat.choose (s + (2 * r - 2)) (2 * r - 2)

/-- The expected generic dimension of `ker d_1`.

For `r >= 2`, this is the closed form
`choose (k + r - 2) (r - 2)`.
-/
def genericKernelDimensionExpected (r k : ℕ) : ℕ :=
  Nat.choose (k + r - 2) (r - 2)

/-- Euler characteristic of the expected rank-general recurrence complex.

This is

`sum_q (-1)^q * choose r q * |I_{k-q}^T|`.

The subtraction in `k - q` is Lean's truncated natural subtraction; this is
harmless for the first scaffold and can later be replaced by a dependent range
over `q <= min r k`.
-/
def recurrenceEulerCharacteristic (r k : ℕ) : ℤ :=
  (Finset.range (r + 1)).sum fun q =>
    ((-1 : ℤ) ^ q)
      * (Nat.choose r q : ℤ)
      * (combIndexCard r (k - q) : ℤ)

/-- Statement that the Euler characteristic gives the expected generic
dimension.

This is the combinatorial target of the eventual generic exactness proof.
-/
def GenericDimensionFormula (r k : ℕ) : Prop :=
  recurrenceEulerCharacteristic r k =
    (genericKernelDimensionExpected r k : ℤ)

/-- The first differential of the recurrence complex. -/
abbrev firstDifferential {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (A : CombCoeffSpace r (s + 1)) :
    Fin r → CombCoeffSpace r s :=
  dOne n w A

/-- Membership in the kernel of the first differential. -/
def InFirstKernel {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (A : CombCoeffSpace r (s + 1)) : Prop :=
  firstDifferential n w A = fun _j => (fun _β => 0)

theorem recurrence_iff_in_first_kernel {r s : ℕ}
    (n : ℝ)
    (w : Fin r → ℝ)
    (A : CombCoeffSpace r (s + 1)) :
    RankRecurrenceAtLevel n w A
      ↔
    InFirstKernel n w A := by
  unfold InFirstKernel firstDifferential
  exact recurrence_iff_dOne_zero n w A

/-- Package for a future proof of generic exactness. -/
structure GenericExactnessData (r k : ℕ) : Prop where
  euler_formula : GenericDimensionFormula r k

end LeftComb

end Calculus
end Operators
end Ambient
end ConformalStructure
