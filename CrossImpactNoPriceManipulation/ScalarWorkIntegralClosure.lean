/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.DeterministicExponentialEnergy
import CrossImpactNoPriceManipulation.DynamicSpectralTrajectoryClosure
/-!
# Scalar work-integral closure
This file derives the complete scalar exponential-mode work identity directly
from the pointwise power identity and interval integration by parts.
It then instantiates that identity for projected spectral coordinates of
vector-valued exponential-memory trajectories.
-/
namespace CrossImpactNoPriceManipulation
section ScalarWorkIntegral
/--
For a scalar exponential-memory state satisfying `x' = u - ρ x`, the work
integral is exactly terminal storage minus initial storage plus integrated
decay.
-/
theorem scalarExponentialMode_workIntegral_energyIdentity
    {a b ρ : ℝ}
    (u x : ℝ → ℝ)
    (hxContinuous : ContinuousOn x (Set.uIcc a b))
    (hODE :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivAt x (u t - ρ * x t) t)
    (hDerivativeIntegrable :
      IntervalIntegrable
        (fun t => u t - ρ * x t)
        MeasureTheory.volume
        a
        b)
    (hPairingIntegrable :
      IntervalIntegrable
        (fun t =>
          ((u t - ρ * x t) * x t) +
            (x t * (u t - ρ * x t)))
        MeasureTheory.volume
        a
        b)
    (hDecayIntegrable :
      IntervalIntegrable
        (fun t => ρ * x t ^ 2)
        MeasureTheory.volume
        a
        b) :
    (∫ t in a..b, u t * x t) =
      scalarModeStorage (x b) -
        scalarModeStorage (x a) +
        (∫ t in a..b, ρ * x t ^ 2) := by
  have hPointwise :
      Set.EqOn
        (fun t => u t * x t)
        (fun t =>
          (2 : ℝ)⁻¹ *
              (((u t - ρ * x t) * x t) +
                (x t * (u t - ρ * x t))) +
            ρ * x t ^ 2)
        (Set.uIcc a b) := by
    intro t _
    exact scalarExponentialMode_pointwisePowerIdentity
      (ρ := ρ)
      (u := u t)
      (x := x t)
  rw [intervalIntegral.integral_congr hPointwise]
  have hSplit :
      (∫ t in a..b,
        (2 : ℝ)⁻¹ *
            (((u t - ρ * x t) * x t) +
              (x t * (u t - ρ * x t))) +
          ρ * x t ^ 2) =
        (∫ t in a..b,
          (2 : ℝ)⁻¹ *
            (((u t - ρ * x t) * x t) +
              (x t * (u t - ρ * x t)))) +
        (∫ t in a..b, ρ * x t ^ 2) := by
    exact intervalIntegral.integral_add
      (hPairingIntegrable.const_mul (2 : ℝ)⁻¹)
      hDecayIntegrable
  rw [hSplit]
  rw [intervalIntegral.integral_const_mul]
  rw [
    scalarExponentialMode_derivativePairing
      u
      x
      hxContinuous
      hODE
      hDerivativeIntegrable
  ]
  unfold scalarModeStorage
  ring
/--
A zero-initial scalar exponential mode with nonnegative decay rate has
nonnegative work integral.
-/
theorem scalarExponentialMode_workIntegral_nonnegative
    {a b ρ : ℝ}
    (u x : ℝ → ℝ)
    (hab : a ≤ b)
    (hρ : 0 ≤ ρ)
    (hInitial : x a = 0)
    (hxContinuous : ContinuousOn x (Set.uIcc a b))
    (hODE :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivAt x (u t - ρ * x t) t)
    (hDerivativeIntegrable :
      IntervalIntegrable
        (fun t => u t - ρ * x t)
        MeasureTheory.volume
        a
        b)
    (hPairingIntegrable :
      IntervalIntegrable
        (fun t =>
          ((u t - ρ * x t) * x t) +
            (x t * (u t - ρ * x t)))
        MeasureTheory.volume
        a
        b)
    (hDecayIntegrable :
      IntervalIntegrable
        (fun t => ρ * x t ^ 2)
        MeasureTheory.volume
        a
        b) :
    0 ≤ ∫ t in a..b, u t * x t := by
  have hDecayNonnegative :
      0 ≤ ∫ t in a..b, ρ * x t ^ 2 := by
    apply intervalIntegral.integral_nonneg hab
    intro t _
    exact scalarExponentialMode_decay_nonnegative hρ
  apply scalarExponentialMode_work_nonnegative
    x
    hInitial
    hDecayNonnegative
  exact scalarExponentialMode_workIntegral_energyIdentity
    u
    x
    hxContinuous
    hODE
    hDerivativeIntegrable
    hPairingIntegrable
    hDecayIntegrable
end ScalarWorkIntegral
section ProjectedCoordinateWorkIntegral
variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
/--
Every spectral coordinate of a zero-initial vector exponential-memory state
has nonnegative scalar work integral.
-/
theorem positiveSpectralCoordinate_workIntegral_nonnegative
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : ℝ → E)
    (a b ρ : ℝ)
    (i : Fin n)
    (hab : a ≤ b)
    (hρ : 0 ≤ ρ)
    (hInitial : x a = 0)
    (hCoordinateContinuous :
      ContinuousOn
        (fun t =>
          positiveSpectralCoordinate T hT n hn i (x t))
        (Set.uIcc a b))
    (hVectorODE :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivAt x (u t - ρ • x t) t)
    (hDerivativeIntegrable :
      IntervalIntegrable
        (fun t =>
          positiveSpectralCoordinate T hT n hn i (u t) -
            ρ *
              positiveSpectralCoordinate T hT n hn i (x t))
        MeasureTheory.volume
        a
        b)
    (hPairingIntegrable :
      IntervalIntegrable
        (fun t =>
          ((positiveSpectralCoordinate T hT n hn i (u t) -
              ρ *
                positiveSpectralCoordinate T hT n hn i (x t)) *
              positiveSpectralCoordinate T hT n hn i (x t)) +
            (positiveSpectralCoordinate T hT n hn i (x t) *
              (positiveSpectralCoordinate T hT n hn i (u t) -
                ρ *
                  positiveSpectralCoordinate T hT n hn i (x t))))
        MeasureTheory.volume
        a
        b)
    (hDecayIntegrable :
      IntervalIntegrable
        (fun t =>
          ρ *
            positiveSpectralCoordinate T hT n hn i (x t) ^ 2)
        MeasureTheory.volume
        a
        b) :
    0 ≤
      ∫ t in a..b,
        positiveSpectralCoordinate T hT n hn i (u t) *
          positiveSpectralCoordinate T hT n hn i (x t) := by
  apply scalarExponentialMode_workIntegral_nonnegative
    (fun t =>
      positiveSpectralCoordinate T hT n hn i (u t))
    (fun t =>
      positiveSpectralCoordinate T hT n hn i (x t))
    hab
    hρ
  · exact positiveSpectralCoordinate_initial_zero
      T hT n hn x a hInitial i
  · exact hCoordinateContinuous
  · intro t ht
    exact positiveSpectralCoordinate_hasDerivAt
      T
      hT
      n
      hn
      u
      x
      ρ
      t
      (hVectorODE t ht)
      i
  · exact hDerivativeIntegrable
  · exact hPairingIntegrable
  · exact hDecayIntegrable
end ProjectedCoordinateWorkIntegral
end CrossImpactNoPriceManipulation
