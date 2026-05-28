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

/-!
# Ovsienko--Redou coefficient indices

The OR bidifferential words are indexed by triples `(a, b, c)` with
`a + b + c = N`, corresponding to

`Δ̃^a(Δ̃^b f · Δ̃^c g)`.
-/

/-- The coefficient index `(a,b,c)` of total degree `N`. -/
structure ORIndex (N : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  sum_eq : a + b + c = N
deriving DecidableEq

namespace ORIndex

/-- The rank-two Laplacian word encoded by an OR index. -/
def toWord {N : ℕ} (I : ORIndex N) : LaplacianWord 2 :=
  BiLaplacianWord.mk I.a I.b I.c

@[simp]
theorem toWord_totalPower {N : ℕ} (I : ORIndex N) :
    I.toWord.totalPower = N := by
  simpa [toWord, BiLaplacianWord.totalPower] using I.sum_eq

/-- Raw finite support for all triples with entries bounded by `N`. -/
def supportRaw (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((((Finset.range (N + 1)).product (Finset.range (N + 1))).product
      (Finset.range (N + 1))).filter
    (fun p => p.1.1 + p.1.2 + p.2 = N))

/-- The canonical finite OR support of all coefficient indices of degree `N`. -/
def support (N : ℕ) : Finset (ORIndex N) := by
  classical
  exact (supportRaw N).attach.image fun p =>
    { a := p.1.1.1
      b := p.1.1.2
      c := p.1.2
      sum_eq := by
        exact (Finset.mem_filter.mp p.2).2 }

theorem support_toWord_totalPower
    {N : ℕ}
    {I : ORIndex N}
    (_hI : I ∈ support N) :
    I.toWord.totalPower = N :=
  I.toWord_totalPower

/-! ## Adjacent moves preserving total degree -/

/-- Move one unit from the output Laplacian power to the first input power. -/
def move_a_to_b {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    ORIndex N where
  a := I.a - 1
  b := I.b + 1
  c := I.c
  sum_eq := by
    have hsum := I.sum_eq
    omega

/-- Move one unit from the output Laplacian power to the second input power. -/
def move_a_to_c {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    ORIndex N where
  a := I.a - 1
  b := I.b
  c := I.c + 1
  sum_eq := by
    have hsum := I.sum_eq
    omega

/-- Move one unit from the first input power to the output Laplacian power. -/
def move_b_to_a {N : ℕ} (I : ORIndex N) (hb : 0 < I.b) :
    ORIndex N where
  a := I.a + 1
  b := I.b - 1
  c := I.c
  sum_eq := by
    have hsum := I.sum_eq
    omega

/-- Move one unit from the second input power to the output Laplacian power. -/
def move_c_to_a {N : ℕ} (I : ORIndex N) (hc : 0 < I.c) :
    ORIndex N where
  a := I.a + 1
  b := I.b
  c := I.c - 1
  sum_eq := by
    have hsum := I.sum_eq
    omega

/-- Move one unit from the first input power to the second input power. -/
def move_b_to_c {N : ℕ} (I : ORIndex N) (hb : 0 < I.b) :
    ORIndex N where
  a := I.a
  b := I.b - 1
  c := I.c + 1
  sum_eq := by
    have hsum := I.sum_eq
    omega

/-- Move one unit from the second input power to the first input power. -/
def move_c_to_b {N : ℕ} (I : ORIndex N) (hc : 0 < I.c) :
    ORIndex N where
  a := I.a
  b := I.b + 1
  c := I.c - 1
  sum_eq := by
    have hsum := I.sum_eq
    omega

@[simp] theorem move_a_to_b_a {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    (I.move_a_to_b ha).a = I.a - 1 := rfl

@[simp] theorem move_a_to_b_b {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    (I.move_a_to_b ha).b = I.b + 1 := rfl

@[simp] theorem move_a_to_b_c {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    (I.move_a_to_b ha).c = I.c := rfl

@[simp] theorem move_a_to_c_a {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    (I.move_a_to_c ha).a = I.a - 1 := rfl

@[simp] theorem move_a_to_c_b {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    (I.move_a_to_c ha).b = I.b := rfl

@[simp] theorem move_a_to_c_c {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    (I.move_a_to_c ha).c = I.c + 1 := rfl

@[simp] theorem move_b_to_a_a {N : ℕ} (I : ORIndex N) (hb : 0 < I.b) :
    (I.move_b_to_a hb).a = I.a + 1 := rfl

@[simp] theorem move_b_to_a_b {N : ℕ} (I : ORIndex N) (hb : 0 < I.b) :
    (I.move_b_to_a hb).b = I.b - 1 := rfl

@[simp] theorem move_b_to_a_c {N : ℕ} (I : ORIndex N) (hb : 0 < I.b) :
    (I.move_b_to_a hb).c = I.c := rfl

@[simp] theorem move_c_to_a_a {N : ℕ} (I : ORIndex N) (hc : 0 < I.c) :
    (I.move_c_to_a hc).a = I.a + 1 := rfl

@[simp] theorem move_c_to_a_b {N : ℕ} (I : ORIndex N) (hc : 0 < I.c) :
    (I.move_c_to_a hc).b = I.b := rfl

@[simp] theorem move_c_to_a_c {N : ℕ} (I : ORIndex N) (hc : 0 < I.c) :
    (I.move_c_to_a hc).c = I.c - 1 := rfl

@[simp] theorem move_b_to_c_a {N : ℕ} (I : ORIndex N) (hb : 0 < I.b) :
    (I.move_b_to_c hb).a = I.a := rfl

@[simp] theorem move_b_to_c_b {N : ℕ} (I : ORIndex N) (hb : 0 < I.b) :
    (I.move_b_to_c hb).b = I.b - 1 := rfl

@[simp] theorem move_b_to_c_c {N : ℕ} (I : ORIndex N) (hb : 0 < I.b) :
    (I.move_b_to_c hb).c = I.c + 1 := rfl

@[simp] theorem move_c_to_b_a {N : ℕ} (I : ORIndex N) (hc : 0 < I.c) :
    (I.move_c_to_b hc).a = I.a := rfl

@[simp] theorem move_c_to_b_b {N : ℕ} (I : ORIndex N) (hc : 0 < I.c) :
    (I.move_c_to_b hc).b = I.b + 1 := rfl

@[simp] theorem move_c_to_b_c {N : ℕ} (I : ORIndex N) (hc : 0 < I.c) :
    (I.move_c_to_b hc).c = I.c - 1 := rfl

/-! ## Arithmetic lemmas for adjacent moves -/

theorem N_sub_b_pos_of_a_pos {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    0 < N - I.b := by
  have hsum := I.sum_eq
  omega

theorem N_sub_c_pos_of_a_pos {N : ℕ} (I : ORIndex N) (ha : 0 < I.a) :
    0 < N - I.c := by
  have hsum := I.sum_eq
  omega

theorem N_sub_b_pred_eq {N : ℕ} (I : ORIndex N) (_ha : 0 < I.a) :
    N - I.b - 1 = N - (I.b + 1) := by
  have hsum := I.sum_eq
  omega

theorem N_sub_c_pred_eq {N : ℕ} (I : ORIndex N) (_ha : 0 < I.a) :
    N - I.c - 1 = N - (I.c + 1) := by
  have hsum := I.sum_eq
  omega

theorem b_succ_add_c {N : ℕ} (I : ORIndex N) :
    I.b + 1 + I.c = I.b + I.c + 1 := by
  omega

theorem b_add_c_succ {N : ℕ} (I : ORIndex N) :
    I.b + (I.c + 1) = I.b + I.c + 1 := by
  omega

end ORIndex

end Calculus
end Operators
end Ambient
end ConformalStructure
