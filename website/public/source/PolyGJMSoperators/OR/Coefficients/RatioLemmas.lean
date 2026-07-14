import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.OR.Coefficients.ClosedFormula

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
# Local ratio data for the regular OR coefficients

The full recurrence proof should be built from local adjacent-index identities.
This file records the first reusable pieces without importing the operator
tangentiality layer.
-/

/-- The first-slot recurrence multiplier appearing in Lemma 3.1. -/
def ORFirstSlotMultiplier
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) : ℚ :=
  2 * w₁ + 2 * w₂ + n - 2 * (N : ℚ) - 2 * I.b - 2 * I.c

/-- The second-slot recurrence multiplier appearing in Lemma 3.1. -/
def ORSecondSlotMultiplier
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) : ℚ :=
  2 * w₁ + 2 * w₂ + n - 2 * (N : ℚ) - 2 * I.b - 2 * I.c

/-- The left factor in the first recurrence equation. -/
def ORFirstSlotLeftFactor
    {N : ℕ}
    (n w₁ : ℚ)
    (I : ORIndex N) : ℚ :=
  2 * w₁ + n - 2 * I.b - 2

/-- The left factor in the second recurrence equation. -/
def ORSecondSlotLeftFactor
    {N : ℕ}
    (n w₂ : ℚ)
    (I : ORIndex N) : ℚ :=
  2 * w₂ + n - 2 * I.c - 2

/--
Expanded form of the Gamma-ratio part after moving one unit from the output
power to the first input power.
-/
theorem ORRegularA_move_a_to_b_expanded
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N)
    (ha : 0 < I.a) :
    ORRegularA n w₁ w₂ (I.move_a_to_b ha) =
      pochhammerQ (ORAlpha N n w₁ w₂) ((I.b + 1) + I.c)
        * pochhammerQ (ORBeta N n w₁) (N - (I.b + 1))
        * pochhammerQ (ORGamma N n w₂) (N - I.c) := by
  simp [ORRegularA]

/--
Expanded form of the Gamma-ratio part after moving one unit from the output
power to the second input power.
-/
theorem ORRegularA_move_a_to_c_expanded
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N)
    (ha : 0 < I.a) :
    ORRegularA n w₁ w₂ (I.move_a_to_c ha) =
      pochhammerQ (ORAlpha N n w₁ w₂) (I.b + (I.c + 1))
        * pochhammerQ (ORBeta N n w₁) (N - I.b)
        * pochhammerQ (ORGamma N n w₂) (N - (I.c + 1)) := by
  simp [ORRegularA]

/--
The first recurrence equation for the Gamma-ratio part. This is the local
identity from which the first-slot defect cancellation proof should proceed.
-/
def ORRegularAFirstRecurrence
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) : Prop :=
  ∀ ha : 0 < I.a,
    ORFirstSlotLeftFactor n w₁ I
      * ORRegularA n w₁ w₂ (I.move_a_to_b ha)
      =
    -ORFirstSlotMultiplier n w₁ w₂ I
      * ORRegularA n w₁ w₂ I

/--
The second recurrence equation for the Gamma-ratio part. This is the local
identity from which the second-slot defect cancellation proof should proceed.
-/
def ORRegularASecondRecurrence
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) : Prop :=
  ∀ ha : 0 < I.a,
    ORSecondSlotLeftFactor n w₂ I
      * ORRegularA n w₁ w₂ (I.move_a_to_c ha)
      =
    -ORSecondSlotMultiplier n w₁ w₂ I
      * ORRegularA n w₁ w₂ I

theorem ORFirstSlotLeftFactor_eq_two_beta_last
    {N : ℕ}
    (n w₁ : ℚ)
    (I : ORIndex N)
    (ha : 0 < I.a) :
    ORFirstSlotLeftFactor n w₁ I =
      2 * (ORBeta N n w₁ + ((N - (I.b + 1) : ℕ) : ℚ)) := by
  have hsum := I.sum_eq
  have hle : I.b + 1 ≤ N := by omega
  unfold ORFirstSlotLeftFactor ORBeta ORHalfShift
  rw [Nat.cast_sub hle]
  norm_num [Nat.cast_add]
  ring

theorem ORSecondSlotLeftFactor_eq_two_gamma_last
    {N : ℕ}
    (n w₂ : ℚ)
    (I : ORIndex N)
    (ha : 0 < I.a) :
    ORSecondSlotLeftFactor n w₂ I =
      2 * (ORGamma N n w₂ + ((N - (I.c + 1) : ℕ) : ℚ)) := by
  have hsum := I.sum_eq
  have hle : I.c + 1 ≤ N := by omega
  unfold ORSecondSlotLeftFactor ORGamma ORHalfShift
  rw [Nat.cast_sub hle]
  norm_num [Nat.cast_add]
  ring

theorem neg_ORSlotMultiplier_eq_two_alpha_last
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) :
    -ORFirstSlotMultiplier n w₁ w₂ I =
      2 * (ORAlpha N n w₁ w₂ + ((I.b + I.c : ℕ) : ℚ)) := by
  unfold ORFirstSlotMultiplier ORAlpha ORHalfShift
  norm_num [Nat.cast_add]
  ring

theorem neg_ORSecondSlotMultiplier_eq_two_alpha_last
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) :
    -ORSecondSlotMultiplier n w₁ w₂ I =
      2 * (ORAlpha N n w₁ w₂ + ((I.b + I.c : ℕ) : ℚ)) := by
  unfold ORSecondSlotMultiplier ORAlpha ORHalfShift
  norm_num [Nat.cast_add]
  ring

theorem ORRegularA_firstRecurrence
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) :
    ORRegularAFirstRecurrence n w₁ w₂ I := by
  intro ha
  unfold ORRegularA ORFirstSlotLeftFactor ORFirstSlotMultiplier
  simp only [ORIndex.move_a_to_b_b, ORIndex.move_a_to_b_c]
  rw [ORIndex.b_succ_add_c]
  rw [pochhammerQ_succ]
  have hNb : 0 < N - I.b := I.N_sub_b_pos_of_a_pos ha
  rw [pochhammerQ_eq_pred_mul (ORBeta N n w₁) hNb]
  rw [ORIndex.N_sub_b_pred_eq I ha]
  rw [show
      2 * w₁ + n - 2 * (I.b : ℚ) - 2 =
        2 * (ORBeta N n w₁ + ((N - (I.b + 1) : ℕ) : ℚ)) by
    exact ORFirstSlotLeftFactor_eq_two_beta_last n w₁ I ha]
  rw [show
      -(2 * w₁ + 2 * w₂ + n - 2 * (N : ℚ) - 2 * (I.b : ℚ) - 2 * (I.c : ℚ)) =
        2 * (ORAlpha N n w₁ w₂ + ((I.b + I.c : ℕ) : ℚ)) by
    exact neg_ORSlotMultiplier_eq_two_alpha_last n w₁ w₂ I]
  ring

theorem ORRegularA_secondRecurrence
    {N : ℕ}
    (n w₁ w₂ : ℚ)
    (I : ORIndex N) :
    ORRegularASecondRecurrence n w₁ w₂ I := by
  intro ha
  unfold ORRegularA ORSecondSlotLeftFactor ORSecondSlotMultiplier
  simp only [ORIndex.move_a_to_c_b, ORIndex.move_a_to_c_c]
  rw [ORIndex.b_add_c_succ]
  rw [pochhammerQ_succ]
  have hNc : 0 < N - I.c := I.N_sub_c_pos_of_a_pos ha
  rw [pochhammerQ_eq_pred_mul (ORGamma N n w₂) hNc]
  rw [ORIndex.N_sub_c_pred_eq I ha]
  rw [show
      2 * w₂ + n - 2 * (I.c : ℚ) - 2 =
        2 * (ORGamma N n w₂ + ((N - (I.c + 1) : ℕ) : ℚ)) by
    exact ORSecondSlotLeftFactor_eq_two_gamma_last n w₂ I ha]
  rw [show
      -(2 * w₁ + 2 * w₂ + n - 2 * (N : ℚ) - 2 * (I.b : ℚ) - 2 * (I.c : ℚ)) =
        2 * (ORAlpha N n w₁ w₂ + ((I.b + I.c : ℕ) : ℚ)) by
    exact neg_ORSecondSlotMultiplier_eq_two_alpha_last n w₁ w₂ I]
  ring

/-- The regular Gamma-ratio coefficient satisfies both Lemma 3.1 recurrences. -/
theorem ORRegularA_satisfiesLemma31Recurrences
    {N : ℕ}
    (n w₁ w₂ : ℚ) :
    (∀ I : ORIndex N, ORRegularAFirstRecurrence n w₁ w₂ I)
      ∧
    (∀ I : ORIndex N, ORRegularASecondRecurrence n w₁ w₂ I) := by
  constructor
  · intro I
    exact ORRegularA_firstRecurrence n w₁ w₂ I
  · intro I
    exact ORRegularA_secondRecurrence n w₁ w₂ I

end Calculus
end Operators
end Ambient
end ConformalStructure
