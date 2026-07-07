/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib.Probability.Martingale.Basic
import CrossImpactNoPriceManipulation.DeterministicMartingaleBridge
/-!
# Predictable finite-step martingale bridge
This file extends the deterministic unaffected-price bridge to random
predictable strategy coefficients. Each coefficient is measurable with
respect to the information available before its corresponding martingale
increment, and each increment has conditional expectation zero.
-/
namespace CrossImpactNoPriceManipulation
open scoped BigOperators MeasureTheory
/-- Expected unaffected-price cost for a finite predictable strategy. -/
noncomputable def predictableUnaffectedPriceCost
    {Ω ι : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (steps : Finset ι)
    (position priceIncrement : ι → Ω → ℝ) : ℝ :=
  ∫ ω, ∑ i ∈ steps, position i ω * priceIncrement i ω ∂μ
/-- Zero expected unaffected-price cost for a predictable finite strategy. -/
theorem predictableUnaffectedPriceCost_eq_zero
    {Ω ι : Type*}
    {mΩ : MeasurableSpace Ω}
    (μ : MeasureTheory.Measure Ω)
    (steps : Finset ι)
    (information : ι → MeasurableSpace Ω)
    (hInformationLe : ∀ i, information i ≤ mΩ)
    (position priceIncrement : ι → Ω → ℝ)
    (hSigmaFinite :
      ∀ i, MeasureTheory.SigmaFinite (μ.trim (hInformationLe i)))
    (hPredictable :
      ∀ i ∈ steps, StronglyMeasurable[information i] (position i))
    (hIncrementIntegrable :
      ∀ i ∈ steps, MeasureTheory.Integrable (priceIncrement i) μ)
    (hProductIntegrable :
      ∀ i ∈ steps,
        MeasureTheory.Integrable
          (fun ω => position i ω * priceIncrement i ω) μ)
    (hConditionalMeanZero :
      ∀ i ∈ steps,
        μ[priceIncrement i | information i] =ᵐ[μ] 0) :
    predictableUnaffectedPriceCost
      μ steps position priceIncrement = 0 := by
  unfold predictableUnaffectedPriceCost
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i hi
    letI : MeasureTheory.SigmaFinite
        (μ.trim (hInformationLe i)) :=
      hSigmaFinite i
    calc
      ∫ ω, position i ω * priceIncrement i ω ∂μ =
          ∫ ω,
            μ[
              fun ω => position i ω * priceIncrement i ω
              | information i
            ] ω
          ∂μ := by
            symm
            exact MeasureTheory.integral_condExp
              (hInformationLe i)
      _ =
          ∫ ω,
            position i ω *
              μ[priceIncrement i | information i] ω
          ∂μ := by
            exact MeasureTheory.integral_congr_ae
              (MeasureTheory.condExp_mul_of_stronglyMeasurable_left
                (hPredictable i hi)
                (hProductIntegrable i hi)
                (hIncrementIntegrable i hi))
      _ = 0 := by
            have hZero :
                (fun ω =>
                  position i ω *
                    μ[priceIncrement i | information i] ω) =ᵐ[μ]
                  0 := by
              filter_upwards [hConditionalMeanZero i hi] with ω hω
              simp [hω]
            rw [MeasureTheory.integral_congr_ae hZero]
            simp
  · intro i hi
    exact hProductIntegrable i hi
/-- Predictable-strategy no-price-manipulation for continuous power-law impact. -/
theorem concreteContinuousPowerLaw_predictableNoPriceManipulation
    {Ω ι E : Type*}
    {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (μ : MeasureTheory.Measure Ω)
    (steps : Finset ι)
    (information : ι → MeasurableSpace Ω)
    (hInformationLe : ∀ i, information i ≤ mΩ)
    (position priceIncrement : ι → Ω → ℝ)
    {α : ℝ}
    {operator : ℝ → E →ₗ[ℝ] E}
    {hPositive : ∀ r, (operator r).IsPositive}
    {n : ℕ}
    {hn : Module.finrank ℝ E = n}
    {u x : ℝ → ℝ → E}
    {a b : ℝ}
    (hSigmaFinite :
      ∀ i, MeasureTheory.SigmaFinite (μ.trim (hInformationLe i)))
    (hPredictable :
      ∀ i ∈ steps, StronglyMeasurable[information i] (position i))
    (hIncrementIntegrable :
      ∀ i ∈ steps, MeasureTheory.Integrable (priceIncrement i) μ)
    (hProductIntegrable :
      ∀ i ∈ steps,
        MeasureTheory.Integrable
          (fun ω => position i ω * priceIncrement i ω) μ)
    (hConditionalMeanZero :
      ∀ i ∈ steps,
        μ[priceIncrement i | information i] =ᵐ[μ] 0)
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
      (predictableUnaffectedPriceCost
        μ steps position priceIncrement)
      (concreteContinuousPowerLawWork
        α operator hPositive n hn u x a b) := by
  apply concreteContinuousPowerLaw_financialNoPriceManipulation
  · exact predictableUnaffectedPriceCost_eq_zero
      μ
      steps
      information
      hInformationLe
      position
      priceIncrement
      hSigmaFinite
      hPredictable
      hIncrementIntegrable
      hProductIntegrable
      hConditionalMeanZero
  · exact hConcrete
end CrossImpactNoPriceManipulation
