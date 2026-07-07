/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.SufficientFinancialStage

/-!
# Continuous-time analytic transfer layer

This file formalizes the integral-positivity and storage-transfer results
used by the sufficient no-price-manipulation theorem.

It covers ordinary interval integrals and continuous mixture integrals.
The stochastic integration-by-parts identity remains an explicit hypothesis
because a suitable continuous-time stochastic-integral construction is not
currently supplied by the imported mathlib interface.
-/

namespace CrossImpactNoPriceManipulation

open MeasureTheory
open scoped Interval

/-- A scalar cost obtained by integrating its instantaneous rate over time. -/
noncomputable def timeIntegratedCost
    (a b : ℝ)
    (costRate : ℝ → ℝ) : ℝ :=
  ∫ t in a..b, costRate t

/-- A pointwise nonnegative cost rate has nonnegative integrated cost. -/
theorem timeIntegratedCost_nonnegative
    {a b : ℝ}
    (hab : a ≤ b)
    (costRate : ℝ → ℝ)
    (hCostRate : ∀ t, 0 ≤ costRate t) :
    0 ≤ timeIntegratedCost a b costRate := by
  unfold timeIntegratedCost
  exact intervalIntegral.integral_nonneg_of_forall hab hCostRate

/-- A round trip has zero time-integrated trading rate. -/
def IsTimeRoundTrip
    (a b : ℝ)
    (tradingRate : ℝ → ℝ) : Prop :=
  (∫ t in a..b, tradingRate t) = 0

/-- The integrated storage-dissipation form of a passive-state cost. -/
def passiveIntegratedCost
    (initialStorage finalStorage integratedDissipation : ℝ) : ℝ :=
  finalStorage - initialStorage + integratedDissipation

/-- A storage increase and nonnegative integrated dissipation imply passivity. -/
theorem passiveIntegratedCost_nonnegative
    {initialStorage finalStorage integratedDissipation : ℝ}
    (hStorage : initialStorage ≤ finalStorage)
    (hDissipation : 0 ≤ integratedDissipation) :
    0 ≤ passiveIntegratedCost
      initialStorage finalStorage integratedDissipation := by
  unfold passiveIntegratedCost
  linarith

/--
If the time-integrated power equals storage increase plus dissipation, then
the integrated power is nonnegative.
-/
theorem passive_power_integral_nonnegative
    {a b initialStorage finalStorage integratedDissipation : ℝ}
    (power : ℝ → ℝ)
    (hIdentity :
      (∫ t in a..b, power t) =
        passiveIntegratedCost
          initialStorage finalStorage integratedDissipation)
    (hStorage : initialStorage ≤ finalStorage)
    (hDissipation : 0 ≤ integratedDissipation) :
    0 ≤ ∫ t in a..b, power t := by
  rw [hIdentity]
  exact passiveIntegratedCost_nonnegative hStorage hDissipation

section ContinuousMixtures

variable {ρ : Type*}
variable [MeasurableSpace ρ]

/-- A continuous mixture cost is the integral of its mode costs. -/
noncomputable def continuousMixtureCost
    (μ : Measure ρ)
    (modeCost : ρ → ℝ) : ℝ :=
  ∫ r, modeCost r ∂μ

/-- A pointwise nonnegative family of mode costs has nonnegative mixture cost. -/
theorem continuousMixtureCost_nonnegative
    (μ : Measure ρ)
    (modeCost : ρ → ℝ)
    (hMode : ∀ r, 0 ≤ modeCost r) :
    0 ≤ continuousMixtureCost μ modeCost := by
  unfold continuousMixtureCost
  exact MeasureTheory.integral_nonneg hMode

/--
A continuous family of nonnegative storage increases and dissipations has
nonnegative aggregate memory cost.
-/
theorem continuousModeMemoryCost_nonnegative
    (μ : Measure ρ)
    (storageIncrease dissipation : ρ → ℝ)
    (hStorage : ∀ r, 0 ≤ storageIncrease r)
    (hDissipation : ∀ r, 0 ≤ dissipation r) :
    0 ≤ continuousMixtureCost μ
      (fun r => storageIncrease r + dissipation r) := by
  apply continuousMixtureCost_nonnegative
  intro r
  exact add_nonneg (hStorage r) (hDissipation r)

/--
Transfer nonnegativity through an exact integral representation of a kernel
or cost quantity.
-/
theorem nonnegative_of_continuousMixture_representation
    (μ : Measure ρ)
    (modeCost : ρ → ℝ)
    (representedCost : ℝ)
    (hRepresentation :
      representedCost = continuousMixtureCost μ modeCost)
    (hMode : ∀ r, 0 ≤ modeCost r) :
    0 ≤ representedCost := by
  rw [hRepresentation]
  exact continuousMixtureCost_nonnegative μ modeCost hMode

end ContinuousMixtures

/--
Power-law specialization: once a power-law cost is represented as a
continuous mixture of nonnegative exponential-mode costs, it is
nonnegative.
-/
theorem powerLawCost_nonnegative
    {ρ : Type*}
    [MeasurableSpace ρ]
    (μ : Measure ρ)
    (exponentialModeCost : ρ → ℝ)
    (powerLawCost : ℝ)
    (hGammaRepresentation :
      powerLawCost = continuousMixtureCost μ exponentialModeCost)
    (hModes : ∀ r, 0 ≤ exponentialModeCost r) :
    0 ≤ powerLawCost :=
  nonnegative_of_continuousMixture_representation
    μ exponentialModeCost powerLawCost hGammaRepresentation hModes

/--
Concrete continuous-time sufficient composition theorem.

The hypotheses provide the already-derived analytic identities for the
linear-memory and passive-state terms. The theorem verifies their final
combination with instantaneous impact and the zero-mean unaffected-price
bridge.
-/
theorem continuousTime_sufficientFinancialNoPriceManipulation
    {linearMemoryCost initialStorage finalStorage
      integratedStateDissipation instantaneousCost
      expectedUnaffectedCost : ℝ}
    (hLinear : 0 ≤ linearMemoryCost)
    (hStorage : initialStorage ≤ finalStorage)
    (hStateDissipation : 0 ≤ integratedStateDissipation)
    (hInstantaneous : 0 ≤ instantaneousCost)
    (hUnaffected : expectedUnaffectedCost = 0) :
    0 ≤ expectedExecutionCost
      expectedUnaffectedCost
      (totalImpactCost
        linearMemoryCost
        (passiveIntegratedCost
          initialStorage
          finalStorage
          integratedStateDissipation)
        instantaneousCost) := by
  apply expectedExecutionCost_nonnegative hUnaffected
  apply totalImpactCost_nonnegative
  · exact hLinear
  · exact passiveIntegratedCost_nonnegative
      hStorage hStateDissipation
  · exact hInstantaneous

/--
Martingale bridge stated at the exact interface currently required by the
financial theorem: integration by parts has reduced the unaffected-price
term to a zero-expectation stochastic integral.
-/
theorem martingaleBridge_from_zeroExpectation
    {expectedUnaffectedCost expectedImpactCost : ℝ}
    (hStochasticIntegralMeanZero : expectedUnaffectedCost = 0)
    (hImpact : 0 ≤ expectedImpactCost) :
    0 ≤ expectedExecutionCost
      expectedUnaffectedCost expectedImpactCost :=
  expectedExecutionCost_nonnegative
    hStochasticIntegralMeanZero hImpact

end CrossImpactNoPriceManipulation
