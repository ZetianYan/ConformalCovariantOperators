import ConformalCovariantOperators.Ambient.PE.Applications.CaseKhaitanLinTyrrellYuan
import ConformalCovariantOperators.Ambient.PE.Invariants.Pfaffian
import ConformalCovariantOperators.Ambient.PE.Renormalization.Volume

open Classical
open scoped BigOperators

noncomputable section

universe u v

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# Pfaffian application

This file records the Theorem 1.4 specialization to `Pf_ell(W)` and assembles
the formal Theorem 1.1 statement from explicit Albin and Pfaffian-reduction
certificates.
-/

/-- Theorem 1.4 specialized to `Pf_ell(W)`. -/
theorem renormalizedIntegral_WeylPfLike
    (X : PESpace.{u, v})
    [InvariantEvaluationModel]
    [EinsteinAmbientLaplacianFormula]
    [CaseEinsteinEvaluationFormula]
    [PfLikeStraightness]
    [P : PERenormalizationPackage X]
    (ell : Nat)
    (hn : Even X.bulkDim)
    (hellPos : 1 <= ell)
    (hellRange : ell <= X.bulkDim / 2) :
    RenormalizedCurvatureIntegral (P.cutoffData (WeylPfLike ell))
      =
    CaseCoeff X.bulkDim ell
      * P.convergentIntegral (P_l_n ell X.bulkDim) := by
  exact theorem_1_4_formal
    X ell
    (WeylPfLike ell)
    (AmbientRmPfLike ell)
    hn hellPos hellRange
    (WeylPfLike_straightenable ell)
    (WeylPfLike_weight ell)

/-- Coefficient of the `P_(ell,n)` term in Theorem 1.1. -/
def PfaffianCaseCoeff (n ell : Nat) : Real :=
  (Nat.factorial (ell - 1) : Real)
    /
  (((-2 : Real) ^ (n / 2 - ell))
    * (Nat.factorial (n / 2 - 1) : Real))

/-- Coefficient of the renormalized volume term in Theorem 1.1. -/
def PfaffianVolumeCoeff (n : Nat) : Real :=
  ((-1 : Real) ^ (n / 2))
    * (doubleFactorial (n - 1) : Real)

/--
The two external inputs for the Pfaffian application:

* Albin's renormalized Gauss--Bonnet identity;
* the Einstein Pfaffian reduction obtained by applying Theorem 1.4 termwise.
-/
structure PfaffianApplicationData
    (X : PESpace.{u, v})
    [InvariantEvaluationModel]
    [P : PERenormalizationPackage X] where
  volumeData : PEVolumeCutoffData X
  volume_normalForm :
    volumeData.normalForm = P.normalForm
  eulerCharacteristic : Int
  albinRenormalizedPfaffian :
    P.RInt (FullPfaffianInvariant X.bulkDim)
      =
    (2 * Real.pi) ^ (X.bulkDim / 2)
      * (eulerCharacteristic : Real)
  pfaffianReduction :
    P.RInt (FullPfaffianInvariant X.bulkDim)
      =
    PfaffianVolumeCoeff X.bulkDim
        * RenormalizedVolume volumeData
      +
    ∑ ell ∈ Finset.Icc 2 (X.bulkDim / 2),
      PfaffianCaseCoeff X.bulkDim ell
        * P.convergentIntegral (P_l_n ell X.bulkDim)

/-- Formal Theorem 1.1. -/
theorem theorem_1_1_formal
    (X : PESpace.{u, v})
    [InvariantEvaluationModel]
    [P : PERenormalizationPackage X]
    (D : PfaffianApplicationData X) :
    (2 * Real.pi) ^ (X.bulkDim / 2)
        * (D.eulerCharacteristic : Real)
      =
    PfaffianVolumeCoeff X.bulkDim
        * RenormalizedVolume D.volumeData
      +
    ∑ ell ∈ Finset.Icc 2 (X.bulkDim / 2),
      PfaffianCaseCoeff X.bulkDim ell
        * P.convergentIntegral (P_l_n ell X.bulkDim) := by
  rw [← D.albinRenormalizedPfaffian]
  exact D.pfaffianReduction

end PE
end Ambient
end ConformalStructure
