/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import CrossImpactNoPriceManipulation.PowerLawGammaClosure
import CrossImpactNoPriceManipulation.ConcreteFiniteExponentialMixture
/-!
# Continuous concrete power-law work
This file connects the concrete nonnegative exponential-mode work theorem to
the Gamma-weighted continuous power-law mixture.
-/
namespace CrossImpactNoPriceManipulation
variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
/-- Gamma-weighted continuous aggregate of concrete exponential-mode work. -/
noncomputable def concreteContinuousPowerLawWork
    (α : ℝ)
    (operator : ℝ → E →ₗ[ℝ] E)
    (hPositive : ∀ r, (operator r).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : ℝ → ℝ → E)
    (a b : ℝ) : ℝ :=
  ∫ r : ℝ in Set.Ioi 0,
    powerLawGammaDensity α r *
      concretePositiveOperatorModeWork
        operator hPositive n hn u x a b r
/--
The Gamma-weighted continuous family of concrete exponential modes is
integrable and has nonnegative aggregate work.
-/
theorem concreteContinuousPowerLawWork_integrable_nonnegative
    (α : ℝ)
    (hα : 0 < α)
    (operator : ℝ → E →ₗ[ℝ] E)
    (hPositive : ∀ r, (operator r).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : ℝ → ℝ → E)
    (a b : ℝ)
    (hab : a ≤ b)
    (hInitial :
      ∀ r ∈ Set.Ioi (0 : ℝ), x r a = 0)
    (hCoordinateContinuous :
      ∀ r ∈ Set.Ioi (0 : ℝ), ∀ i,
        ContinuousOn
          (fun t =>
            positiveSpectralCoordinate
              (operator r) (hPositive r) n hn i (x r t))
          (Set.uIcc a b))
    (hVectorODE :
      ∀ r ∈ Set.Ioi (0 : ℝ),
        ∀ t ∈ Set.Ioo (min a b) (max a b),
          HasDerivAt
            (x r)
            (u r t - r • x r t)
            t)
    (hDerivativeIntegrable :
      ∀ r ∈ Set.Ioi (0 : ℝ), ∀ i,
        IntervalIntegrable
          (fun t =>
            positiveSpectralCoordinate
                (operator r) (hPositive r) n hn i (u r t) -
              r *
                positiveSpectralCoordinate
                  (operator r) (hPositive r) n hn i (x r t))
          MeasureTheory.volume
          a
          b)
    (hPairingIntegrable :
      ∀ r ∈ Set.Ioi (0 : ℝ), ∀ i,
        IntervalIntegrable
          (fun t =>
            ((positiveSpectralCoordinate
                  (operator r) (hPositive r) n hn i (u r t) -
                r *
                  positiveSpectralCoordinate
                    (operator r) (hPositive r) n hn i (x r t)) *
              positiveSpectralCoordinate
                (operator r) (hPositive r) n hn i (x r t)) +
            (positiveSpectralCoordinate
                  (operator r) (hPositive r) n hn i (x r t) *
              (positiveSpectralCoordinate
                  (operator r) (hPositive r) n hn i (u r t) -
                r *
                  positiveSpectralCoordinate
                    (operator r) (hPositive r) n hn i (x r t))))
          MeasureTheory.volume
          a
          b)
    (hDecayIntegrable :
      ∀ r ∈ Set.Ioi (0 : ℝ), ∀ i,
        IntervalIntegrable
          (fun t =>
            r *
              positiveSpectralCoordinate
                (operator r) (hPositive r) n hn i (x r t) ^ 2)
          MeasureTheory.volume
          a
          b)
    (hAggregateIntegrable :
      MeasureTheory.IntegrableOn
        (fun r =>
          powerLawGammaDensity α r *
            concretePositiveOperatorModeWork
              operator hPositive n hn u x a b r)
        (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
        (fun r =>
          powerLawGammaDensity α r *
            concretePositiveOperatorModeWork
              operator hPositive n hn u x a b r)
        (Set.Ioi 0) ∧
      0 ≤ concreteContinuousPowerLawWork
        α operator hPositive n hn u x a b := by
  refine ⟨hAggregateIntegrable, ?_⟩
  unfold concreteContinuousPowerLawWork
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro r hr
  apply mul_nonneg
  · exact powerLawGammaDensity_nonnegative hα hr.le
  · exact concretePositiveOperatorModeWork_nonnegative
      operator
      hPositive
      n
      hn
      u
      x
      a
      b
      (fun s => s)
      r
      hab
      hr.le
      (hInitial r hr)
      (hCoordinateContinuous r hr)
      (hVectorODE r hr)
      (hDerivativeIntegrable r hr)
      (hPairingIntegrable r hr)
      (hDecayIntegrable r hr)
/--
Financial no-price-manipulation composition for concrete continuous
power-law work.
-/
theorem concreteContinuousPowerLaw_financialNoPriceManipulation
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {expectedUnaffectedCost α : ℝ}
    {operator : ℝ → E →ₗ[ℝ] E}
    {hPositive : ∀ r, (operator r).IsPositive}
    {n : ℕ}
    {hn : Module.finrank ℝ E = n}
    {u x : ℝ → ℝ → E}
    {a b : ℝ}
    (hUnaffected : expectedUnaffectedCost = 0)
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
      expectedUnaffectedCost
      (concreteContinuousPowerLawWork
        α operator hPositive n hn u x a b) := by
  exact expectedExecutionCost_nonnegative hUnaffected hConcrete.2
end CrossImpactNoPriceManipulation
