import Mathlib

open Classical

noncomputable section

universe u

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Finite Laurent--log expansions

This syntax records the data relevant to finite-part renormalization:

`sum_m a_m epsilon^m + L log(epsilon) + o(1)`.

Analytic assertions about the remainder are intentionally separated from the
finite algebraic data in this file.
-/

/-- A Laurent expansion with one logarithmic coefficient and finite support. -/
structure LaurentLogExpansion (R : Type u) [Zero R] where
  coeff : Int -> R
  logCoeff : R
  lowerBound : Int
  upperBound : Int
  lower_le_upper : lowerBound <= upperBound
  coeff_vanish_lt :
    forall m : Int, m < lowerBound -> coeff m = 0
  coeff_vanish_gt :
    forall m : Int, upperBound < m -> coeff m = 0

namespace LaurentLogExpansion

variable {R : Type u} [Zero R] (E : LaurentLogExpansion R)

/-- The finite interval containing every potentially nonzero Laurent term. -/
def activeExponents : Finset Int :=
  Finset.Icc E.lowerBound E.upperBound

theorem coeff_eq_zero_of_lt
    {m : Int}
    (hm : m < E.lowerBound) :
    E.coeff m = 0 :=
  E.coeff_vanish_lt m hm

theorem coeff_eq_zero_of_gt
    {m : Int}
    (hm : E.upperBound < m) :
    E.coeff m = 0 :=
  E.coeff_vanish_gt m hm

/-- Parity through order `N`, measured by the absolute exponent. -/
def EvenExpansionToOrder (N : Nat) : Prop :=
  forall m : Int,
    m.natAbs <= N ->
    Odd m ->
    E.coeff m = 0

/-- Odd parity through order `N`, measured by the absolute exponent. -/
def OddExpansionToOrder (N : Nat) : Prop :=
  forall m : Int,
    m.natAbs <= N ->
    Even m ->
    E.coeff m = 0

end LaurentLogExpansion

/-- Top-level spelling of even parity for renormalization applications. -/
def EvenExpansionToOrder
    {R : Type u}
    [Zero R]
    (E : LaurentLogExpansion R)
    (N : Nat) :
    Prop :=
  E.EvenExpansionToOrder N

/-- Top-level spelling of odd parity for renormalization applications. -/
def OddExpansionToOrder
    {R : Type u}
    [Zero R]
    (E : LaurentLogExpansion R)
    (N : Nat) :
    Prop :=
  E.OddExpansionToOrder N

end PE
end Ambient
end ConformalStructure
