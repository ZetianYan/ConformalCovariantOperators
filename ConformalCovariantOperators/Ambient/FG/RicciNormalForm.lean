import ConformalCovariantOperators.Ambient.FG.Christoffel

open Classical
open scoped BigOperators

noncomputable section

universe w

namespace ConformalStructure
namespace Ambient
namespace FG

variable {ι : Type w}

/-!
# Ricci equations in Fefferman-Graham normal form

This file records the symbolic component formulas for the Ricci tensor of a
straight normal-form ambient metric.  It is intentionally component-level: the
full tensor-calculus derivation will later prove the certificate fields from
the Christoffel formulas.
-/

/-- Component data appearing in the FG normal-form Ricci equations. -/
structure RicciNormalFormComponents (ι : Type w) extends NormalInverseMetricComponents ι where
  /-- The formal base dimension `n`. -/
  baseDim : ℝ
  /-- First `rho` derivative `g'_{ij}`. -/
  gPrime : ι → ι → ℝ
  /-- Second `rho` derivative `g''_{ij}`. -/
  gDoublePrime : ι → ι → ℝ
  /-- Ricci tensor of the slice metric `g_rho`. -/
  baseRicci : ι → ι → ℝ
  /-- Covariant derivative `nabla_k g'_{ij}` with respect to `g_rho`. -/
  covDerivGPrime : ι → ι → ι → ℝ

namespace RicciNormalFormComponents

variable [Fintype ι]

/-- The trace `g^{kl} g'_{kl}`. -/
def tracePrime (C : RicciNormalFormComponents ι) : ℝ :=
  ∑ k : ι, ∑ l : ι, C.gInv k l * C.gPrime k l

/-- The trace `g^{kl} g''_{kl}`. -/
def traceDoublePrime (C : RicciNormalFormComponents ι) : ℝ :=
  ∑ k : ι, ∑ l : ι, C.gInv k l * C.gDoublePrime k l

/-- The quadratic term `g^{kl} g'_{ik} g'_{jl}`. -/
def quadraticPrime (C : RicciNormalFormComponents ι) (i j : ι) : ℝ :=
  ∑ k : ι, ∑ l : ι, C.gInv k l * C.gPrime i k * C.gPrime j l

/-- The scalar quadratic trace `g^{kl} g^{pq} g'_{kp} g'_{lq}`. -/
def quadraticTracePrime (C : RicciNormalFormComponents ι) : ℝ :=
  ∑ k : ι, ∑ l : ι, ∑ p : ι, ∑ q : ι,
    C.gInv k l * C.gInv p q * C.gPrime k p * C.gPrime l q

/-- The base-base part of the FG normal-form Ricci equation. -/
def FG_RicciEq_ij (C : RicciNormalFormComponents ι) (i j : ι) : ℝ :=
  C.rho * C.gDoublePrime i j
    - C.rho * C.quadraticPrime i j
    + (1 / 2 : ℝ) * C.rho * C.tracePrime * C.gPrime i j
    - (C.baseDim / 2 - 1) * C.gPrime i j
    - (1 / 2 : ℝ) * C.tracePrime * C.g i j
    + C.baseRicci i j

/-- The base-infinity part of the FG normal-form Ricci equation. -/
def FG_RicciEq_iInf (C : RicciNormalFormComponents ι) (i : ι) : ℝ :=
  (1 / 2 : ℝ) *
    (∑ k : ι, ∑ l : ι,
      C.gInv k l * (C.covDerivGPrime k i l - C.covDerivGPrime i k l))

/-- The infinity-infinity part of the FG normal-form Ricci equation. -/
def FG_RicciEq_infInf (C : RicciNormalFormComponents ι) : ℝ :=
  -(1 / 2 : ℝ) * C.traceDoublePrime
    + (1 / 4 : ℝ) * C.quadraticTracePrime

end RicciNormalFormComponents

/--
A certificate that a symbolic ambient Ricci tensor satisfies the FG normal-form
component formulas.
-/
structure RicciNormalFormCertificate
    [Fintype ι]
    (C : RicciNormalFormComponents ι) where
  /-- The ambient Ricci tensor components. -/
  Ricci : AmbientIndex ι → AmbientIndex ι → ℝ
  /-- In straight normal form, the `0I` components vanish. -/
  ricci_zero_left : ∀ I : AmbientIndex ι, Ricci AmbientIndex.zero I = 0
  /-- In straight normal form, the `I0` components vanish. -/
  ricci_zero_right : ∀ I : AmbientIndex ι, Ricci I AmbientIndex.zero = 0
  /-- The base-base normal-form formula. -/
  ricci_base_base :
    ∀ i j : ι,
      Ricci (AmbientIndex.base i) (AmbientIndex.base j)
        = C.FG_RicciEq_ij i j
  /-- The base-infinity normal-form formula. -/
  ricci_base_inf :
    ∀ i : ι,
      Ricci (AmbientIndex.base i) AmbientIndex.inf
        = C.FG_RicciEq_iInf i
  /-- The infinity-base normal-form formula. -/
  ricci_inf_base :
    ∀ i : ι,
      Ricci AmbientIndex.inf (AmbientIndex.base i)
        = C.FG_RicciEq_iInf i
  /-- The infinity-infinity normal-form formula. -/
  ricci_inf_inf :
    Ricci AmbientIndex.inf AmbientIndex.inf
      = C.FG_RicciEq_infInf

theorem ricci_zero_left_normal_form
    [Fintype ι]
    {C : RicciNormalFormComponents ι}
    (H : RicciNormalFormCertificate C)
    (I : AmbientIndex ι) :
    H.Ricci AmbientIndex.zero I = 0 :=
  H.ricci_zero_left I

theorem ricci_base_base_normal_form
    [Fintype ι]
    {C : RicciNormalFormComponents ι}
    (H : RicciNormalFormCertificate C)
    (i j : ι) :
    H.Ricci (AmbientIndex.base i) (AmbientIndex.base j)
      = C.FG_RicciEq_ij i j :=
  H.ricci_base_base i j

theorem ricci_base_inf_normal_form
    [Fintype ι]
    {C : RicciNormalFormComponents ι}
    (H : RicciNormalFormCertificate C)
    (i : ι) :
    H.Ricci (AmbientIndex.base i) AmbientIndex.inf
      = C.FG_RicciEq_iInf i :=
  H.ricci_base_inf i

theorem ricci_inf_inf_normal_form
    [Fintype ι]
    {C : RicciNormalFormComponents ι}
    (H : RicciNormalFormCertificate C) :
    H.Ricci AmbientIndex.inf AmbientIndex.inf
      = C.FG_RicciEq_infInf :=
  H.ricci_inf_inf

end FG
end Ambient
end ConformalStructure
