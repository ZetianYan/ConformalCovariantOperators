import Mathlib
import ConformalCovariantOperators.PolyGJMSoperators.LinearCombination
import ConformalCovariantOperators.PolyGJMSoperators.Bidifferential

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
# Laplacian words

A rank-r Laplacian word encodes an operator of the form

`Δ̃^a(∏ᵢ Δ̃^{bᵢ} fᵢ)`.

This file only formalizes the language and the weight theorem under an abstract
product-homogeneity hypothesis. Tangential defect calculations are intentionally
left for a later layer.
-/

/-- A rank-r Laplacian monomial word. -/
structure LaplacianWord (r : ℕ) where
  outputPower : ℕ
  inputPower : Fin r → ℕ
deriving DecidableEq

namespace LaplacianWord

variable {CalConf}

/-- The product of input-side Laplacian powers. -/
def inputProduct
    {r : ℕ}
    (W : LaplacianWord r)
    (CalConf : Calculus Conf)
    (F : CalConf.MultiInput r) :
    Function Conf :=
  fun U => ∏ i : Fin r, CalConf.lapPow (W.inputPower i) (F i) U

/-- The rank-r multi-operator represented by a Laplacian word. -/
def toOperator
    {r : ℕ}
    (W : LaplacianWord r)
    (CalConf : Calculus Conf) :
    CalConf.MultiOperator r :=
  fun F => CalConf.lapPow W.outputPower (W.inputProduct CalConf F)

/-- Total Laplacian degree in the word. -/
def totalPower
    {r : ℕ}
    (W : LaplacianWord r) : ℕ :=
  W.outputPower + ∑ i : Fin r, W.inputPower i

/-- Expected output weight from applying the word to inputs of multiweight `w`. -/
def expectedOutputWeight
    {r : ℕ}
    (W : LaplacianWord r)
    (CalConf : Calculus Conf)
    (w : Fin r → ℝ) : ℝ :=
  CalConf.totalWeight w - 2 * (W.totalPower : ℝ)

@[simp]
theorem inputProduct_apply
    {r : ℕ}
    (W : LaplacianWord r)
    (F : CalConf.MultiInput r)
    (U : Conf.AmbientBundle) :
    W.inputProduct CalConf F U =
      ∏ i : Fin r, CalConf.lapPow (W.inputPower i) (F i) U := by
  rfl

@[simp]
theorem toOperator_apply
    {r : ℕ}
    (W : LaplacianWord r)
    (F : CalConf.MultiInput r) :
    W.toOperator CalConf F =
      CalConf.lapPow W.outputPower (W.inputProduct CalConf F) := by
  rfl

end LaplacianWord

/--
Abstract product homogeneity identity.

This is the isolated assumption needed to prove weight mapping for Laplacian
words. Later it can be proved from an `X_mul` / Leibniz rule.
-/
structure ProductHomogeneityIdentities : Prop where
  product_homogeneous :
    ∀ {r : ℕ} (A : Fin r → Function Conf) (w : Fin r → ℝ),
      (∀ i : Fin r, CalConf.IsXHomogeneous (w i) (A i)) →
        CalConf.IsXHomogeneous
          (CalConf.totalWeight w)
          (fun U => ∏ i : Fin r, A i U)

namespace LaplacianWord

variable {CalConf}

/-- The input product has the sum of the shifted input weights. -/
theorem inputProduct_mapsWeight
    (H : CalConf.AlgebraicIdentities)
    (Hprod : CalConf.ProductHomogeneityIdentities)
    {r : ℕ}
    (W : LaplacianWord r)
    {w : Fin r → ℝ}
    {F : CalConf.MultiInput r}
    (hF : CalConf.IsMultiHomogeneous w F) :
    CalConf.IsXHomogeneous
      (CalConf.totalWeight
        (fun i : Fin r => w i - 2 * (W.inputPower i : ℝ)))
      (W.inputProduct CalConf F) := by
  apply Hprod.product_homogeneous
  intro i
  have hpow := CalConf.lapPow_isXHomogeneous H (W.inputPower i) (hF i)
  simpa [LapPowHasWeight] using hpow

/-- A Laplacian word maps its input multiweight to its expected output weight. -/
theorem mapsWeights
    (H : CalConf.AlgebraicIdentities)
    (Hprod : CalConf.ProductHomogeneityIdentities)
    {r : ℕ}
    (W : LaplacianWord r)
    (w : Fin r → ℝ) :
    CalConf.MapsWeights
      (W.toOperator CalConf)
      w
      (W.expectedOutputWeight CalConf w) := by
  intro F hF
  have hprod := W.inputProduct_mapsWeight H Hprod hF
  have hout := CalConf.lapPow_isXHomogeneous H W.outputPower hprod
  unfold LapPowHasWeight at hout
  convert hout using 1
  unfold expectedOutputWeight totalPower totalWeight
  rw [Finset.sum_sub_distrib]
  rw [Nat.cast_add, Nat.cast_sum]
  rw [← Finset.mul_sum]
  ring_nf

end LaplacianWord

/-! ## Rank-two Laplacian words -/

namespace BiLaplacianWord

/-- The rank-two word `(a; b, c)`, i.e. `Δ̃^a(Δ̃^b f · Δ̃^c g)`. -/
def mk (a b c : ℕ) : LaplacianWord 2 where
  outputPower := a
  inputPower := fun i => if i = 0 then b else c

@[simp]
theorem mk_outputPower
    (a b c : ℕ) :
    (mk a b c).outputPower = a := by
  rfl

@[simp]
theorem mk_inputPower_zero
    (a b c : ℕ) :
    (mk a b c).inputPower 0 = b := by
  simp [mk]

@[simp]
theorem mk_inputPower_one
    (a b c : ℕ) :
    (mk a b c).inputPower 1 = c := by
  norm_num [mk]

theorem totalPower
    (a b c : ℕ) :
    (mk a b c).totalPower = a + b + c := by
  unfold LaplacianWord.totalPower mk
  rw [Fin.sum_univ_two]
  simp
  omega

theorem expectedOutputWeight
    (a b c : ℕ)
    (w₁ w₂ : ℝ) :
    (mk a b c).expectedOutputWeight CalConf (CalConf.biWeights w₁ w₂)
      =
    w₁ + w₂ - 2 * ((a + b + c : ℕ) : ℝ) := by
  unfold LaplacianWord.expectedOutputWeight
  rw [CalConf.totalWeight_biWeights]
  rw [totalPower]

theorem toOperator_pairInput_apply
    (a b c : ℕ)
    (f g : Function Conf) :
    (mk a b c).toOperator CalConf (CalConf.pairInput f g)
      =
    CalConf.lapPow a
      (fun U =>
        CalConf.lapPow b f U * CalConf.lapPow c g U) := by
  unfold LaplacianWord.toOperator LaplacianWord.inputProduct mk
  congr 1
  funext U
  rw [Fin.prod_univ_two]
  simp [pairInput]

end BiLaplacianWord

/-! ## Rank-three Laplacian words -/

namespace TriLaplacianWord

/-- The rank-three word `(a; b, c, d)`. -/
def mk (a b c d : ℕ) : LaplacianWord 3 where
  outputPower := a
  inputPower := fun i =>
    if i = 0 then b else if i = 1 then c else d

@[simp]
theorem mk_outputPower
    (a b c d : ℕ) :
    (mk a b c d).outputPower = a := by
  rfl

@[simp]
theorem mk_inputPower_zero
    (a b c d : ℕ) :
    (mk a b c d).inputPower 0 = b := by
  simp [mk]

@[simp]
theorem mk_inputPower_one
    (a b c d : ℕ) :
    (mk a b c d).inputPower 1 = c := by
  norm_num [mk]

@[simp]
theorem mk_inputPower_two
    (a b c d : ℕ) :
    (mk a b c d).inputPower 2 = d := by
  unfold mk
  change (if (2 : Fin 3) = 0 then b else if (2 : Fin 3) = 1 then c else d) = d
  rw [if_neg (by decide : (2 : Fin 3) ≠ 0)]
  rw [if_neg (by decide : (2 : Fin 3) ≠ 1)]

end TriLaplacianWord

/-! ## Finite combinations of bidifferential Laplacian words -/

/-- Data for a finite bidifferential linear combination of Laplacian words. -/
structure BiLaplacianCombinationData where
  support : Finset (LaplacianWord 2)
  coeff : LaplacianWord 2 → ℝ

namespace BiLaplacianCombinationData

/-- The bidifferential operator associated to a finite Laplacian-word sum. -/
def toOperator
    (D : BiLaplacianCombinationData)
    (CalConf : Calculus Conf) :
    CalConf.BiOperator :=
  CalConf.operatorSum D.support D.coeff
    (fun W => W.toOperator CalConf)

@[simp]
theorem toOperator_apply
    (D : BiLaplacianCombinationData)
    (F : CalConf.BiInput)
    (U : Conf.AmbientBundle) :
    D.toOperator CalConf F U =
      ∑ W ∈ D.support,
        D.coeff W * W.toOperator CalConf F U := by
  rfl

end BiLaplacianCombinationData

end Calculus
end Operators
end Ambient
end ConformalStructure
