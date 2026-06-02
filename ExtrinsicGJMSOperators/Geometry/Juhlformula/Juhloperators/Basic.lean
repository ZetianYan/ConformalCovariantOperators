import Mathlib

open Classical
open scoped BigOperators

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace Operators
namespace Calculus
namespace Juhl

/-- An ordered composition of `N`.

Mathematically this is a finite ordered tuple
`I = (I_1, ..., I_r)` with positive entries and total sum `N`.
-/
structure Composition (N : Nat) where
  parts : List Nat
  positive : ∀ n, n ∈ parts → 0 < n
  sum_eq : parts.sum = N

namespace Composition

variable {N : Nat}

/-- The length of a composition. -/
def length (I : Composition N) : Nat :=
  I.parts.length

/-- The empty composition of `0`. -/
def nil : Composition 0 where
  parts := []
  positive := by
    intro n hn
    cases hn
  sum_eq := by
    simp

/-- The singleton composition `(N)`, for `N > 0`. -/
def singleton (N : Nat) (hN : 0 < N) : Composition N where
  parts := [N]
  positive := by
    intro n hn
    simp at hn
    subst n
    exact hN
  sum_eq := by
    simp

@[simp]
theorem nil_parts :
    (nil : Composition 0).parts = [] := by
  rfl

@[simp]
theorem singleton_parts
    (N : Nat) (hN : 0 < N) :
    (singleton N hN).parts = [N] := by
  rfl

@[simp]
theorem singleton_length
    (N : Nat) (hN : 0 < N) :
    (singleton N hN).length = 1 := by
  rfl

/-- The first nontrivial two-part composition `(a,b)`. -/
def pair
    (a b : Nat)
    (ha : 0 < a)
    (hb : 0 < b) :
    Composition (a + b) where
  parts := [a, b]
  positive := by
    intro n hn
    simp at hn
    rcases hn with rfl | rfl
    · exact ha
    · exact hb
  sum_eq := by
    simp

@[simp]
theorem pair_parts
    (a b : Nat)
    (ha : 0 < a)
    (hb : 0 < b) :
    (pair a b ha hb).parts = [a, b] := by
  rfl

end Composition

end Juhl
end Calculus
end Operators
end Ambient
end ConformalStructure
