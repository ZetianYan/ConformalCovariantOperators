import ConformalCovariantOperators.Ambient.PE.Invariants.NaturalDivergence
import ConformalCovariantOperators.Ambient.PE.EinsteinEquation
import ConformalCovariantOperators.Ambient.PE.Renormalization.CurvatureIntegral

open Classical

noncomputable section

universe u v w

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Renormalized divergence vanishing

`PERenormalizationPackage` is the analytic interface needed by the formal proof
of Theorem 1.4.  It is connected explicitly to the Phase B cutoff expansion.
-/

/-- Analytic and functorial data for renormalized invariant integrals on a PE space. -/
class PERenormalizationPackage
    (X : PESpace.{u, v})
    [InvariantEvaluationModel] where
  /-- The fixed PE normal form on which all integrals are evaluated. -/
  normalForm : PoincareNormalFormData.{u, v, w} X
  /-- The fixed normal form satisfies the PE Einstein equation. -/
  poincareEinstein : IsPoincareEinstein normalForm
  /-- Cutoff data realizing each symbolic scalar invariant. -/
  cutoffData :
    forall I : ScalarInvariant,
      CurvatureIntegralCutoffData X I
  /-- Every cutoff integral uses the fixed normal form. -/
  cutoffData_normalForm :
    forall I : ScalarInvariant,
      (cutoffData I).normalForm = normalForm
  /-- Renormalized integral functional. -/
  RInt : ScalarInvariant -> Real
  /-- The abstract functional is the Phase B finite-part construction. -/
  RInt_eq_phaseB :
    forall I : ScalarInvariant,
      RInt I = RenormalizedCurvatureIntegral (cutoffData I)
  /-- Ordinary convergent integral for sufficiently decaying invariants. -/
  convergentIntegral : ScalarInvariant -> Real
  /-- Rational linearity. -/
  linear_qsmul :
    forall (c : Rat) (I : ScalarInvariant),
      RInt (ScalarInvariant.qsmul c I) = (c : Real) * RInt I
  /-- Lemma 4.1. -/
  divergence_zero :
    Even X.bulkDim ->
    forall F : OneFormInvariant,
      2 - (X.bulkDim : Int) <= F.1.weight ->
      RInt (divInvariant F) = 0
  /-- Renormalized integrals depend only on the class modulo divergences. -/
  moduloDivergence_eq :
    forall I J : ScalarInvariant,
      InvariantEvaluationModel.EqualModuloDivergence I J ->
      RInt I = RInt J
  /-- Lemma 3.2 after integration on the PE Einstein metric. -/
  associated_integral_eq :
    forall
      (I : ScalarInvariant)
      (Itilde : AmbientScalarInvariant),
      ScalarStraightenable I Itilde ->
      RInt I = RInt (restrictToEinsteinSlice Itilde)
  /-- A weight `-n` conformal invariant has an ordinary convergent integral. -/
  critical_weight_converges :
    forall I : ScalarInvariant,
      I.1.weight = -(X.bulkDim : Int) ->
      IsScalarConformalInvariant I ->
      RInt I = convergentIntegral I

/-- The renormalized integral supplied by the package. -/
def renormalizedIntegral
    (X : PESpace)
    [InvariantEvaluationModel]
    [P : PERenormalizationPackage X]
    (I : ScalarInvariant) :
    Real :=
  P.RInt I

/-- The package agrees with the finite part defined in Phase B. -/
theorem renormalizedIntegral_eq_phaseB
    (X : PESpace)
    [InvariantEvaluationModel]
    [P : PERenormalizationPackage X]
    (I : ScalarInvariant) :
    renormalizedIntegral X I
      =
    RenormalizedCurvatureIntegral (P.cutoffData I) :=
  P.RInt_eq_phaseB I

/-- Lemma 4.1 for a natural divergence carrying the required weight witness. -/
theorem renormalizedIntegral_naturalDivergence_eq_zero
    (X : PESpace)
    [InvariantEvaluationModel]
    [P : PERenormalizationPackage X]
    (hn : Even X.bulkDim)
    (I : ScalarInvariant)
    (hDiv :
      NaturalDivergenceAtWeight
        I
        (2 - (X.bulkDim : Int))) :
    renormalizedIntegral X I = 0 := by
  rcases hDiv with ⟨F, rfl, hWeight⟩
  exact P.divergence_zero hn F hWeight

end PE
end Ambient
end ConformalStructure
