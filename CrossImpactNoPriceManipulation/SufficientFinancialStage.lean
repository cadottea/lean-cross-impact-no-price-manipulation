/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.ExactLinearStage
/-!
# Sufficient financial no-price-manipulation theorem
This file formalizes the algebraic and finite-mode energy core of the
sufficient no-price-manipulation theorem.
The analytic realization of the individual terms as time integrals,
continuous exponential mixtures, power-law kernels, ordinary differential
equations, and stochastic integrals is intentionally separated from this
logical composition layer.
-/
namespace CrossImpactNoPriceManipulation
/--
The impact cost is the sum of the linear-memory, passive-state, and
instantaneous-impact contributions.
-/
def totalImpactCost
    (linearCost stateCost instantaneousCost : ℝ) : ℝ :=
  linearCost + stateCost + instantaneousCost
/--
Nonnegative linear-memory, passive-state, and instantaneous-impact
contributions imply nonnegative total impact cost.
-/
theorem totalImpactCost_nonnegative
    {linearCost stateCost instantaneousCost : ℝ}
    (hLinear : 0 ≤ linearCost)
    (hState : 0 ≤ stateCost)
    (hInstantaneous : 0 ≤ instantaneousCost) :
    0 ≤ totalImpactCost linearCost stateCost instantaneousCost := by
  unfold totalImpactCost
  positivity
/--
A passive-state contribution decomposed into storage increase and
nonnegative dissipation is nonnegative whenever final storage is at least
initial storage.
-/
theorem passiveStateCost_nonnegative
    {initialStorage finalStorage dissipation : ℝ}
    (hStorage : initialStorage ≤ finalStorage)
    (hDissipation : 0 ≤ dissipation) :
    0 ≤ (finalStorage - initialStorage) + dissipation := by
  linarith
/--
A zero-initial-storage passive state has nonnegative cost whenever final
storage and dissipation are nonnegative.
-/
theorem passiveStateCost_nonnegative_from_zero
    {finalStorage dissipation : ℝ}
    (hFinalStorage : 0 ≤ finalStorage)
    (hDissipation : 0 ≤ dissipation) :
    0 ≤ finalStorage + dissipation := by
  positivity
section FiniteExponentialMixture
variable {ι : Type*}
/--
The energy contribution of a finite family of exponential memory modes is
the sum of each mode's storage increase and dissipation.
-/
def finiteModeMemoryCost
    (modes : Finset ι)
    (storageIncrease dissipation : ι → ℝ) : ℝ :=
  ∑ i ∈ modes, (storageIncrease i + dissipation i)
/--
A finite exponential mixture has nonnegative memory cost when every mode has
nonnegative storage increase and nonnegative dissipation.
-/
theorem finiteModeMemoryCost_nonnegative
    (modes : Finset ι)
    (storageIncrease dissipation : ι → ℝ)
    (hStorage : ∀ i ∈ modes, 0 ≤ storageIncrease i)
    (hDissipation : ∀ i ∈ modes, 0 ≤ dissipation i) :
    0 ≤ finiteModeMemoryCost modes storageIncrease dissipation := by
  unfold finiteModeMemoryCost
  apply Finset.sum_nonneg
  intro i hi
  exact add_nonneg (hStorage i hi) (hDissipation i hi)
/--
The finite-mode memory contribution, passive nonlinear-state contribution,
and instantaneous contribution combine into a nonnegative impact cost.
-/
theorem finiteMixture_totalImpactCost_nonnegative
    (modes : Finset ι)
    (storageIncrease dissipation : ι → ℝ)
    {stateCost instantaneousCost : ℝ}
    (hStorage : ∀ i ∈ modes, 0 ≤ storageIncrease i)
    (hDissipation : ∀ i ∈ modes, 0 ≤ dissipation i)
    (hState : 0 ≤ stateCost)
    (hInstantaneous : 0 ≤ instantaneousCost) :
    0 ≤ totalImpactCost
      (finiteModeMemoryCost modes storageIncrease dissipation)
      stateCost
      instantaneousCost := by
  apply totalImpactCost_nonnegative
  · exact finiteModeMemoryCost_nonnegative
      modes storageIncrease dissipation hStorage hDissipation
  · exact hState
  · exact hInstantaneous
end FiniteExponentialMixture
/--
Expected execution cost is the sum of the expected unaffected-price
contribution and expected impact cost.
-/
def expectedExecutionCost
    (expectedUnaffectedCost expectedImpactCost : ℝ) : ℝ :=
  expectedUnaffectedCost + expectedImpactCost
/--
If the unaffected-price contribution has zero expectation and expected impact
cost is nonnegative, then expected execution cost is nonnegative.
-/
theorem expectedExecutionCost_nonnegative
    {expectedUnaffectedCost expectedImpactCost : ℝ}
    (hUnaffected : expectedUnaffectedCost = 0)
    (hImpact : 0 ≤ expectedImpactCost) :
    0 ≤ expectedExecutionCost expectedUnaffectedCost expectedImpactCost := by
  unfold expectedExecutionCost
  simpa [hUnaffected] using hImpact
/--
Abstract sufficient financial no-price-manipulation theorem.
The assumptions correspond to:
* nonnegative symmetrized linear-memory cost on round trips;
* a passive nonlinear-state storage-dissipation identity;
* nonnegative instantaneous impact;
* zero expected unaffected-price contribution.
-/
theorem sufficientFinancialNoPriceManipulation
    {linearCost initialStorage finalStorage stateDissipation
      instantaneousCost expectedUnaffectedCost : ℝ}
    (hLinear : 0 ≤ linearCost)
    (hStorage : initialStorage ≤ finalStorage)
    (hStateDissipation : 0 ≤ stateDissipation)
    (hInstantaneous : 0 ≤ instantaneousCost)
    (hUnaffected : expectedUnaffectedCost = 0) :
    0 ≤ expectedExecutionCost
      expectedUnaffectedCost
      (totalImpactCost
        linearCost
        ((finalStorage - initialStorage) + stateDissipation)
        instantaneousCost) := by
  apply expectedExecutionCost_nonnegative hUnaffected
  apply totalImpactCost_nonnegative
  · exact hLinear
  · exact passiveStateCost_nonnegative hStorage hStateDissipation
  · exact hInstantaneous
/--
Finite-exponential-mixture specialization of the sufficient financial
no-price-manipulation theorem.
-/
theorem finiteMixture_sufficientFinancialNoPriceManipulation
    {ι : Type*}
    (modes : Finset ι)
    (storageIncrease dissipation : ι → ℝ)
    {stateCost instantaneousCost expectedUnaffectedCost : ℝ}
    (hStorage : ∀ i ∈ modes, 0 ≤ storageIncrease i)
    (hDissipation : ∀ i ∈ modes, 0 ≤ dissipation i)
    (hState : 0 ≤ stateCost)
    (hInstantaneous : 0 ≤ instantaneousCost)
    (hUnaffected : expectedUnaffectedCost = 0) :
    0 ≤ expectedExecutionCost
      expectedUnaffectedCost
      (totalImpactCost
        (finiteModeMemoryCost modes storageIncrease dissipation)
        stateCost
        instantaneousCost) := by
  apply expectedExecutionCost_nonnegative hUnaffected
  exact finiteMixture_totalImpactCost_nonnegative
    modes storageIncrease dissipation
    hStorage hDissipation hState hInstantaneous
end CrossImpactNoPriceManipulation
