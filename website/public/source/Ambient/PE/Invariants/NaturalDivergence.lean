import ConformalCovariantOperators.Ambient.PE.Invariants.LaplacianRecursion

open Classical

noncomputable section

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Natural divergences

This file records the symbolic conclusion used in Lemma 4.1 and the statement
interface for Proposition 3.10.
-/

/-- A scalar invariant represented as the divergence of a rank-one invariant. -/
def NaturalDivergence (I : ScalarInvariant) : Prop :=
  exists F : OneFormInvariant, I = divInvariant F

/-- A natural divergence whose one-form has a prescribed lower weight bound. -/
def NaturalDivergenceAtWeight
    (I : ScalarInvariant)
    (lowerWeight : Int) :
    Prop :=
  exists F : OneFormInvariant,
    I = divInvariant F
      ∧
    lowerWeight <= F.1.weight

theorem NaturalDivergenceAtWeight.toNaturalDivergence
    {I : ScalarInvariant}
    {lowerWeight : Int}
    (h : NaturalDivergenceAtWeight I lowerWeight) :
    NaturalDivergence I := by
  rcases h with ⟨F, hI, _hWeight⟩
  exact ⟨F, hI⟩

/-- Dilation-field annihilation of the last ambient tensor index. -/
def XAnnihilatesLastIndex
    [InvariantEvaluationModel]
    (I : AmbientInvariant) :
    Prop :=
  InvariantEvaluationModel.XAnnihilatesLastIndex I

/-- The scalar ambient expression occurring in Proposition 3.10. -/
def proposition310Invariant
    (n k : Nat)
    (Ttilde : AmbientOneFormInvariant) :
    ScalarInvariant :=
  restrictToEinsteinSlice
    (ambientLaplacianIter
      (n / 2 - k - 1)
      (ambientDivInvariant Ttilde))

/--
Semantic interface for the cone-decomposition argument in Proposition 3.10.

Its eventual instance will use `AmbientPEBridge.ambient_metric_cone_decomposition`.
-/
class AmbientRankOneDivergenceRule
    [InvariantEvaluationModel] : Prop where
  proposition310 :
    forall
      (n k : Nat)
      (Ttilde : AmbientOneFormInvariant),
      Even n ->
      Ttilde.1.weight = -2 * (k : Int) ->
      2 - (n : Int) <= Ttilde.1.weight ->
      XAnnihilatesLastIndex Ttilde.1 ->
      NaturalDivergence (proposition310Invariant n k Ttilde)

/-- Proposition 3.10 as exposed by the semantic cone-decomposition rule. -/
theorem ambient_rank_one_divergence_is_natural_divergence
    [InvariantEvaluationModel]
    [AmbientRankOneDivergenceRule]
    (n k : Nat)
    (Ttilde : AmbientOneFormInvariant)
    (hn : Even n)
    (hWeight : Ttilde.1.weight = -2 * (k : Int))
    (hBound : 2 - (n : Int) <= Ttilde.1.weight)
    (hX : XAnnihilatesLastIndex Ttilde.1) :
    NaturalDivergence (proposition310Invariant n k Ttilde) :=
  AmbientRankOneDivergenceRule.proposition310
    n k Ttilde hn hWeight hBound hX

end PE
end Ambient
end ConformalStructure
