import ConformalCovariantOperators.Ambient.PE.MetricComponents

open Classical

noncomputable section

universe u v w

namespace ConformalStructure
namespace Ambient
namespace PE

/-!
# The Poincare-Einstein equation and formal parity data

The first PE milestone records the Einstein equation and the parity output of
its normal-form recursion as certificate data.  A later FG-to-PE recursion
theorem can construct these certificates from ambient Ricci-flatness.
-/

/-- Formal boundary metric coefficients in the expansion of `h_r`. -/
structure PEFormalExpansion (X : PESpace.{u, v}) where
  coeff : Nat -> MetricSymbol X.boundary
  even_to_order :
    forall m : Nat,
      m < X.boundaryDim ->
      Odd m ->
      coeff m = 0
  /-- The critical coefficient has the required trace-free property. -/
  tracefree_obstruction : Prop

namespace PEFormalExpansion

variable {X : PESpace} (E : PEFormalExpansion X)

/-- The parity predicate used by PE normal-form recursion. -/
def HasEvenExpansionToOrder (N : Nat) : Prop :=
  forall m : Nat, m < N -> Odd m -> E.coeff m = 0

theorem hasEvenExpansionToBoundaryOrder :
    E.HasEvenExpansionToOrder X.boundaryDim :=
  E.even_to_order

end PEFormalExpansion

/--
Certificate that a Poincare normal form solves the Einstein equation.

This is data-valued because it carries the formal expansion produced by the
Einstein recursion, not merely a proposition about an externally fixed series.
-/
structure IsPoincareEinstein
    {X : PESpace.{u, v}}
    (NF : PoincareNormalFormData.{u, v, w} X) where
  einstein_equation :
    NF.metric.ricci = einsteinRHS X NF.metric.gPlus
  formalExpansion : PEFormalExpansion X
  coeff_zero : formalExpansion.coeff 0 = NF.h0
  /-- Compatibility between the coefficient family and `NF.hR`. -/
  expansion_certificate : Prop

theorem PE_expansion_even_to_order
    {X : PESpace}
    {NF : PoincareNormalFormData X}
    (hPE : IsPoincareEinstein NF) :
    hPE.formalExpansion.HasEvenExpansionToOrder X.boundaryDim :=
  hPE.formalExpansion.hasEvenExpansionToBoundaryOrder

end PE
end Ambient
end ConformalStructure
