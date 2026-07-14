import Mathlib
import ConformalCovariantOperators.Ambient.Ambienttangential

open Classical

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace GJMS

variable {M : Type u}
variable {Conf : ConformalStructure.{u, v} M}
variable (CalConf : Calculus Conf)

/-!
# Basic interface for GJMS-type operators

This file contains only the abstract interface and weight bookkeeping for
GJMS-type operators.

It does **not** prove that powers of the ambient Laplacian are tangential.
That belongs to a later file, for example:

`GJMS/Tangentiality.lean`.

The philosophy is:

* `Ambient.Tangential` defines weighted tangential ambient operators;
* this file packages the special weights relevant to GJMS operators;
* an abstract GJMS operator is a weighted tangential operator whose input and
  output weights are the GJMS critical weights.
-/


/-! ## GJMS weights -/

/--
The critical input weight for the `k`-th GJMS construction.

Mathematically, this is

`k - n / 2`.
-/
def inputWeight (n : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) - n / 2

/--
The output weight of the `k`-th GJMS construction.

Mathematically, this is

`-k - n / 2`.
-/
def outputWeight (n : ℝ) (k : ℕ) : ℝ :=
  - (k : ℝ) - n / 2

/--
The output weight equals the input weight minus `2k`.

This encodes the fact that `Δ̃^k` lowers homogeneity by `2k`.
-/
theorem outputWeight_eq_inputWeight_sub_two_mul
    (n : ℝ) (k : ℕ) :
    outputWeight n k = inputWeight n k - 2 * (k : ℝ) := by
  unfold inputWeight outputWeight
  ring

@[simp]
theorem inputWeight_zero (n : ℝ) :
    inputWeight n 0 = - n / 2 := by
  unfold inputWeight
  ring

@[simp]
theorem outputWeight_zero (n : ℝ) :
    outputWeight n 0 = - n / 2 := by
  unfold outputWeight
  ring

@[simp]
theorem inputWeight_one (n : ℝ) :
    inputWeight n 1 = 1 - n / 2 := by
  unfold inputWeight
  norm_num

@[simp]
theorem outputWeight_one (n : ℝ) :
    outputWeight n 1 = -1 - n / 2 := by
  unfold outputWeight
  norm_num

@[simp]
theorem inputWeight_two (n : ℝ) :
    inputWeight n 2 = 2 - n / 2 := by
  unfold inputWeight
  norm_num

@[simp]
theorem outputWeight_two (n : ℝ) :
    outputWeight n 2 = -2 - n / 2 := by
  unfold outputWeight
  norm_num


/-! ## Weights attached to a fixed ambient calculus -/

/--
The critical input weight for the `k`-th GJMS operator associated to a fixed
ambient calculus.
-/
def calculusInputWeight (k : ℕ) : ℝ :=
  inputWeight CalConf.n k

/--
The output weight for the `k`-th GJMS operator associated to a fixed ambient
calculus.
-/
def calculusOutputWeight (k : ℕ) : ℝ :=
  outputWeight CalConf.n k

theorem calculusOutputWeight_eq_calculusInputWeight_sub_two_mul
    (k : ℕ) :
    calculusOutputWeight CalConf k
      =
    calculusInputWeight CalConf k - 2 * (k : ℝ) := by
  unfold calculusInputWeight calculusOutputWeight
  exact outputWeight_eq_inputWeight_sub_two_mul CalConf.n k

@[simp]
theorem calculusInputWeight_zero :
    calculusInputWeight CalConf 0 = - CalConf.n / 2 := by
  unfold calculusInputWeight inputWeight
  ring

@[simp]
theorem calculusOutputWeight_zero :
    calculusOutputWeight CalConf 0 = - CalConf.n / 2 := by
  unfold calculusOutputWeight outputWeight
  ring

@[simp]
theorem calculusInputWeight_one :
    calculusInputWeight CalConf 1 = 1 - CalConf.n / 2 := by
  unfold calculusInputWeight inputWeight
  ring

@[simp]
theorem calculusOutputWeight_one :
    calculusOutputWeight CalConf 1 = -1 - CalConf.n / 2 := by
  unfold calculusOutputWeight outputWeight
  ring

@[simp]
theorem calculusInputWeight_two :
    calculusInputWeight CalConf 2 = 2 - CalConf.n / 2 := by
  unfold calculusInputWeight inputWeight
  ring

@[simp]
theorem calculusOutputWeight_two :
    calculusOutputWeight CalConf 2 = -2 - CalConf.n / 2 := by
  unfold calculusOutputWeight outputWeight
  ring


/-! ## Abstract GJMS operators -/

/--
An abstract GJMS-type operator of order `2k`.

At the current abstraction level, a GJMS operator is represented by a weighted
tangential ambient operator whose input and output weights are the standard
GJMS weights:

`k - n / 2  →  -k - n / 2`.

The actual construction from `Δ̃^k` is not included in this file.
-/
structure AbstractOperator where
  /-- The integer `k`, so that the differential order should eventually be `2k`. -/
  k : ℕ

  /-- The weighted tangential ambient operator representing the GJMS operator. -/
  toWeightedTangentialOperator :
    CalConf.WeightedTangentialOperator

  /-- The input weight is the GJMS critical input weight. -/
  inputWeight_eq :
    toWeightedTangentialOperator.inputWeight =
      calculusInputWeight CalConf k

  /-- The output weight is the GJMS output weight. -/
  outputWeight_eq :
    toWeightedTangentialOperator.outputWeight =
      calculusOutputWeight CalConf k

namespace AbstractOperator

variable {CalConf}

/-- The expected differential order of the GJMS operator. -/
def order (P : AbstractOperator CalConf) : ℕ :=
  2 * P.k

/-- The input weight of an abstract GJMS operator. -/
def inputWeightOf (P : AbstractOperator CalConf) : ℝ :=
  P.toWeightedTangentialOperator.inputWeight

/-- The output weight of an abstract GJMS operator. -/
def outputWeightOf (P : AbstractOperator CalConf) : ℝ :=
  P.toWeightedTangentialOperator.outputWeight

/-- The underlying ambient operator. -/
def toOperator (P : AbstractOperator CalConf) :
    Operator (Conf := Conf) :=
  P.toWeightedTangentialOperator.toOperator

/-- The underlying ambient operator maps the correct input weight to the output weight. -/
theorem mapsWeight (P : AbstractOperator CalConf) :
    CalConf.MapsHomogeneousWeight
      P.toOperator
      P.inputWeightOf
      P.outputWeightOf := by
  exact P.toWeightedTangentialOperator.mapsWeight

/-- The underlying ambient operator is tangential at its input weight. -/
theorem tangential (P : AbstractOperator CalConf) :
    CalConf.IsTangentialAtWeight
      P.toOperator
      P.inputWeightOf := by
  exact P.toWeightedTangentialOperator.tangential

/-- The input weight is explicitly `k - n / 2`. -/
theorem inputWeightOf_eq (P : AbstractOperator CalConf) :
    P.inputWeightOf = calculusInputWeight CalConf P.k := by
  unfold inputWeightOf
  exact P.inputWeight_eq

/-- The output weight is explicitly `-k - n / 2`. -/
theorem outputWeightOf_eq (P : AbstractOperator CalConf) :
    P.outputWeightOf = calculusOutputWeight CalConf P.k := by
  unfold outputWeightOf
  exact P.outputWeight_eq

/--
The output weight equals the input weight minus `2k`.
-/
theorem outputWeightOf_eq_inputWeightOf_sub_two_mul
    (P : AbstractOperator CalConf) :
    P.outputWeightOf =
      P.inputWeightOf - 2 * (P.k : ℝ) := by
  rw [P.inputWeightOf_eq, P.outputWeightOf_eq]
  exact calculusOutputWeight_eq_calculusInputWeight_sub_two_mul CalConf P.k

end AbstractOperator


/-! ## Families of GJMS operators -/

/--
A formal family of GJMS operators, one for each natural number `k`.

This is useful later when we want to package the whole GJMS sequence.
-/
structure Family where
  operator : ℕ → AbstractOperator CalConf
  operator_k :
    ∀ k : ℕ, (operator k).k = k

namespace Family

variable {CalConf}

/-- The `k`-th GJMS operator in a family. -/
def get (P : Family CalConf) (k : ℕ) :
    AbstractOperator CalConf :=
  P.operator k

@[simp]
theorem get_k (P : Family CalConf) (k : ℕ) :
    (P.get k).k = k := by
  unfold get
  exact P.operator_k k

/-- The expected differential order of the `k`-th operator is `2k`. -/
theorem get_order (P : Family CalConf) (k : ℕ) :
    (P.get k).order = 2 * k := by
  unfold get AbstractOperator.order
  rw [P.operator_k k]

end Family


/-! ## Low-order names -/

/-- The zeroth GJMS operator, formally of order `0`. -/
abbrev P0 {CalConf : Calculus Conf} (P : Family CalConf) : AbstractOperator CalConf :=
  P.get 0

/-- The first nontrivial GJMS operator, formally of order `2`. -/
abbrev P2 {CalConf : Calculus Conf} (P : Family CalConf) : AbstractOperator CalConf :=
  P.get 1

/-- The second nontrivial GJMS operator, formally of order `4`. -/
abbrev P4 {CalConf : Calculus Conf} (P : Family CalConf) : AbstractOperator CalConf :=
  P.get 2

@[simp]
theorem P0_k (P : Family CalConf) :
    (P0 P).k = 0 := by
  unfold P0
  simp [Family.get_k]

@[simp]
theorem P2_k (P : Family CalConf) :
    (P2 P).k = 1 := by
  unfold P2
  simp [Family.get_k]

@[simp]
theorem P4_k (P : Family CalConf) :
    (P4 P).k = 2 := by
  unfold P4
  simp [Family.get_k]

@[simp]
theorem P0_order (P : Family CalConf) :
    (P0 P).order = 0 := by
  unfold P0 AbstractOperator.order
  simp [Family.get_k]

@[simp]
theorem P2_order (P : Family CalConf) :
    (P2 P).order = 2 := by
  unfold P2 AbstractOperator.order
  simp [Family.get_k]

@[simp]
theorem P4_order (P : Family CalConf) :
    (P4 P).order = 4 := by
  unfold P4 AbstractOperator.order
  simp [Family.get_k]


end GJMS
end Calculus
end Operators
end Ambient
end ConformalStructure
