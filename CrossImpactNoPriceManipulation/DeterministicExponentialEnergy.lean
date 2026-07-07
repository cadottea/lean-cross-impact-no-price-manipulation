/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.ContinuousTimeAnalytics
/-!
# Deterministic exponential-memory energy identity
This file derives the scalar exponential-memory energy identity directly from
the differential equation
`x' = u - ρ x`.
The result is the calculus core of the finite exponential-mixture
no-price-manipulation theorem.
-/
namespace CrossImpactNoPriceManipulation
open MeasureTheory
open scoped Interval
/--
The pointwise power identity for one scalar exponential-memory mode.
If `x' = u - ρ x`, then trading power `u x` is the sum of the derivative
pairing and the nonnegative decay contribution `ρ x²`.
-/
theorem scalarExponentialMode_pointwisePowerIdentity
    (ρ u x : ℝ) :
    u * x =
      (2 : ℝ)⁻¹ *
        (((u - ρ * x) * x) + (x * (u - ρ * x))) +
      ρ * x ^ 2 := by
  ring
/--
Integration by parts applied to a scalar exponential-memory state satisfying
`x' = u - ρ x`.
This proves the endpoint identity for the derivative pairing directly from
the differential equation.
-/
theorem scalarExponentialMode_derivativePairing
    {a b ρ : ℝ}
    (u x : ℝ → ℝ)
    (hxContinuous : ContinuousOn x (Set.uIcc a b))
    (hODE :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivAt x (u t - ρ * x t) t)
    (hDerivativeIntegrable :
      IntervalIntegrable
        (fun t => u t - ρ * x t)
        volume
        a
        b) :
    (∫ t in a..b,
      ((u t - ρ * x t) * x t) +
        (x t * (u t - ρ * x t))) =
      x b * x b - x a * x a := by
  exact intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    hxContinuous
    hxContinuous
    hODE
    hODE
    hDerivativeIntegrable
    hDerivativeIntegrable
/--
The decay contribution of a nonnegative exponential rate is pointwise
nonnegative.
-/
theorem scalarExponentialMode_decay_nonnegative
    {ρ x : ℝ}
    (hρ : 0 ≤ ρ) :
    0 ≤ ρ * x ^ 2 := by
  positivity
/--
The storage associated with a scalar exponential-memory state.
-/
noncomputable def scalarModeStorage (x : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * x ^ 2
/-- Scalar exponential-mode storage is nonnegative. -/
theorem scalarModeStorage_nonnegative
    (x : ℝ) :
    0 ≤ scalarModeStorage x := by
  unfold scalarModeStorage
  positivity
/--
The endpoint derivative-pairing identity expressed as a storage difference.
-/
theorem scalarExponentialMode_storageDifference
    {a b ρ : ℝ}
    (u x : ℝ → ℝ)
    (hxContinuous : ContinuousOn x (Set.uIcc a b))
    (hODE :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivAt x (u t - ρ * x t) t)
    (hDerivativeIntegrable :
      IntervalIntegrable
        (fun t => u t - ρ * x t)
        volume
        a
        b) :
    (2 : ℝ)⁻¹ *
        (∫ t in a..b,
          ((u t - ρ * x t) * x t) +
            (x t * (u t - ρ * x t))) =
      scalarModeStorage (x b) - scalarModeStorage (x a) := by
  rw [
    scalarExponentialMode_derivativePairing
      u x hxContinuous hODE hDerivativeIntegrable
  ]
  unfold scalarModeStorage
  ring
/--
A zero-initial scalar exponential mode has a nonnegative terminal storage
contribution.
-/
theorem scalarExponentialMode_terminalStorage_nonnegative
    {a b : ℝ}
    (x : ℝ → ℝ)
    (hInitial : x a = 0) :
    0 ≤ scalarModeStorage (x b) - scalarModeStorage (x a) := by
  rw [hInitial]
  unfold scalarModeStorage
  have hHalf : 0 ≤ (2 : ℝ)⁻¹ := by norm_num
  nlinarith [sq_nonneg (x b)]
/--
Abstract final energy consequence for one scalar exponential mode.
Once the work integral has been rewritten as terminal-minus-initial storage
plus integrated decay, zero initial state and nonnegative decay imply
nonnegative work.
-/
theorem scalarExponentialMode_work_nonnegative
    {a b work integratedDecay : ℝ}
    (x : ℝ → ℝ)
    (hInitial : x a = 0)
    (hDecayNonnegative : 0 ≤ integratedDecay)
    (hEnergy :
      work =
        scalarModeStorage (x b) -
          scalarModeStorage (x a) +
          integratedDecay) :
    0 ≤ work := by
  rw [hEnergy]
  apply add_nonneg
  · exact scalarExponentialMode_terminalStorage_nonnegative x hInitial
  · exact hDecayNonnegative
end CrossImpactNoPriceManipulation
