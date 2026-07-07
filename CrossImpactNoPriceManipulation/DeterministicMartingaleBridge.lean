/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import CrossImpactNoPriceManipulation.ContinuousConcretePowerLawWork
/-!
# Deterministic-strategy martingale bridge
This file proves that a deterministic trading strategy has zero expected
unaffected-price cost when every integrable price increment has mean zero.
It then connects that result directly to the concrete continuous power-law
financial no-price-manipulation theorem.
-/
namespace CrossImpactNoPriceManipulation
open scoped BigOperators
/--
Expected unaffected-price cost for a deterministic finite-step strategy.
-/
noncomputable def deterministicUnaffectedPriceCost
    {Ω ι : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (steps : Finset ι)
    (position : ι → ℝ)
    (priceIncrement : ι → Ω → ℝ) : ℝ :=
  ∫ ω,
    ∑ i ∈ steps, position i * priceIncrement i ω
  ∂μ
/--
A deterministic finite-step strategy has zero expected unaffected-price cost
when each integrable price increment has mean zero.
-/
theorem deterministicUnaffectedPriceCost_eq_zero
    {Ω ι : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (steps : Finset ι)
    (position : ι → ℝ)
    (priceIncrement : ι → Ω → ℝ)
    (hIntegrable :
      ∀ i ∈ steps,
        MeasureTheory.Integrable (priceIncrement i) μ)
    (hMeanZero :
      ∀ i ∈ steps,
        ∫ ω, priceIncrement i ω ∂μ = 0) :
    deterministicUnaffectedPriceCost
      μ steps position priceIncrement = 0 := by
  unfold deterministicUnaffectedPriceCost
  rw [MeasureTheory.integral_finsetSum]
  · simp only [MeasureTheory.integral_const_mul]
    exact Finset.sum_eq_zero fun i hi => by
      rw [hMeanZero i hi, mul_zero]
  · intro i hi
    exact (hIntegrable i hi).const_mul (position i)
/--
Concrete power-law no-price-manipulation theorem with the zero expected
unaffected-price contribution derived from integrable mean-zero increments.
-/
theorem concreteContinuousPowerLaw_martingaleNoPriceManipulation
    {Ω ι E : Type*}
    [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (μ : MeasureTheory.Measure Ω)
    (steps : Finset ι)
    (position : ι → ℝ)
    (priceIncrement : ι → Ω → ℝ)
    {α : ℝ}
    {operator : ℝ → E →ₗ[ℝ] E}
    {hPositive : ∀ r, (operator r).IsPositive}
    {n : ℕ}
    {hn : Module.finrank ℝ E = n}
    {u x : ℝ → ℝ → E}
    {a b : ℝ}
    (hIncrementIntegrable :
      ∀ i ∈ steps,
        MeasureTheory.Integrable (priceIncrement i) μ)
    (hIncrementMeanZero :
      ∀ i ∈ steps,
        ∫ ω, priceIncrement i ω ∂μ = 0)
    (hConcrete :
      MeasureTheory.IntegrableOn
          (fun r =>
            powerLawGammaDensity α r *
              concretePositiveOperatorModeWork
                operator hPositive n hn u x a b r)
          (Set.Ioi 0) ∧
        0 ≤ concreteContinuousPowerLawWork
          α operator hPositive n hn u x a b) :
    0 ≤ expectedExecutionCost
      (deterministicUnaffectedPriceCost
        μ steps position priceIncrement)
      (concreteContinuousPowerLawWork
        α operator hPositive n hn u x a b) := by
  apply concreteContinuousPowerLaw_financialNoPriceManipulation
  · exact deterministicUnaffectedPriceCost_eq_zero
      μ
      steps
      position
      priceIncrement
      hIncrementIntegrable
      hIncrementMeanZero
  · exact hConcrete
end CrossImpactNoPriceManipulation
