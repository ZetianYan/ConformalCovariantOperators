import ConformalCovariantOperators.Ambient.FG.RicciNormalForm

open Classical
open scoped BigOperators

noncomputable section

universe w

namespace ConformalStructure
namespace Ambient
namespace FG

variable {ι : Type w}

/-!
# Finite formal jets of the normal-form metric

The second phase starts with finite jets of the family `g_rho`.  The coefficients
are component-level symmetric two-tensor placeholders.  The first useful FG
output is the first-jet relation `g'|_{rho=0} = 2 P`, where `P` is the Schouten
tensor of the initial metric.
-/

/-- A component-level symmetric two-tensor expression. -/
abbrev Sym2Component (ι : Type w) := ι → ι → ℝ

/-- Symmetry predicate for component-level two-tensors. -/
def SymmetricComponent (T : Sym2Component ι) : Prop :=
  ∀ i j : ι, T i j = T j i

/-- A finite formal metric jet `g_rho = g + rho g^(1) + ... + rho^K g^(K)`. -/
structure FormalMetricJet (ι : Type w) (K : ℕ) where
  /-- Jet coefficients `g^(m)_{ij}` for `0 <= m <= K`. -/
  coeff : Fin (K + 1) → Sym2Component ι
  /-- The initial metric component `g_{ij}`. -/
  baseMetric : Sym2Component ι
  /-- The Schouten tensor component of the initial metric. -/
  schouten : Sym2Component ι
  /-- The zeroth jet is the initial metric. -/
  coeff_zero_eq_base : ∀ i j : ι, coeff ⟨0, Nat.succ_pos K⟩ i j = baseMetric i j

namespace FormalMetricJet

/-- Access the coefficient `g^(m)` using a proof that `m <= K`. -/
def coeffAt (J : FormalMetricJet ι K) (m : ℕ) (hm : m ≤ K) : Sym2Component ι :=
  J.coeff ⟨m, Nat.lt_succ_of_le hm⟩

@[simp]
theorem coeffAt_zero (J : FormalMetricJet ι K) :
    J.coeffAt 0 (Nat.zero_le K) = J.baseMetric := by
  funext i j
  exact J.coeff_zero_eq_base i j

/-- The first jet coefficient, available when `1 <= K`. -/
def firstCoeff (J : FormalMetricJet ι K) (hK : 1 ≤ K) : Sym2Component ι :=
  J.coeffAt 1 hK

end FormalMetricJet

/--
Finite-order FG Ricci conditions for a formal metric jet.

At order at least one, the first-jet relation is recorded as a field.  Later
files can refine this structure by replacing the field with a proof from the
normal-form Ricci equations.
-/
structure SatisfiesFGRicciToOrder
    (J : FormalMetricJet ι K)
    (order : ℕ) : Prop where
  /-- We only impose conditions up to the available finite jet order. -/
  order_le : order ≤ K
  /-- The first Ricci condition gives `g^(1) = 2 P`. -/
  first_jet_eq_two_schouten :
    ∀ horder : 1 ≤ order,
      ∀ i j : ι,
        J.coeffAt 1 (le_trans horder order_le) i j
          = 2 * J.schouten i j

/-- The first FG jet relation `g'|_{rho=0} = 2 P`. -/
theorem FG_first_jet
    (J : FormalMetricJet ι K)
    (H : SatisfiesFGRicciToOrder J 1)
    (i j : ι) :
    J.coeffAt 1 H.order_le i j = 2 * J.schouten i j := by
  simpa using H.first_jet_eq_two_schouten (by norm_num) i j

end FG
end Ambient
end ConformalStructure
