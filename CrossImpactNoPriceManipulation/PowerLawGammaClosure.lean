/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.ContinuousTimeAnalytics
import CrossImpactNoPriceManipulation.ConcreteFiniteExponentialMixture
/-!
# Power-law Gamma closure
This file proves the positive Gamma/Laplace representation of a power-law
kernel. The representation is derived from Mathlib's weighted Gamma-integral
theorem rather than supplied as an assumption.
-/
namespace CrossImpactNoPriceManipulation
/-- The positive Gamma-normalized density used to mix exponential kernels. -/
noncomputable def powerLawGammaDensity
    (α r : ℝ) : ℝ :=
  (Real.Gamma α)⁻¹ * r ^ (α - 1)
/-- The Gamma-normalized continuous exponential mixture at positive lag `t`. -/
noncomputable def powerLawExponentialMixture
    (α t : ℝ) : ℝ :=
  ∫ r : ℝ in Set.Ioi 0,
    powerLawGammaDensity α r * Real.exp (-(t * r))
/-- The Gamma normalizing constant is strictly positive for positive exponent. -/
theorem powerLawGammaDensity_normalizer_positive
    {α : ℝ}
    (hα : 0 < α) :
    0 < (Real.Gamma α)⁻¹ := by
  exact inv_pos.mpr (Real.Gamma_pos_of_pos hα)
/-- The Gamma mixing density is pointwise nonnegative on positive rates. -/
theorem powerLawGammaDensity_nonnegative
    {α r : ℝ}
    (hα : 0 < α)
    (hr : 0 ≤ r) :
    0 ≤ powerLawGammaDensity α r := by
  unfold powerLawGammaDensity
  exact mul_nonneg
    (powerLawGammaDensity_normalizer_positive hα).le
    (Real.rpow_nonneg hr (α - 1))
/--
Exact Gamma/Laplace representation of the positive power-law kernel.
For positive `α` and positive lag `t`, the normalized continuous mixture of
exponentials equals `(1 / t) ^ α`.
-/
theorem powerLawExponentialMixture_eq
    {α t : ℝ}
    (hα : 0 < α)
    (ht : 0 < t) :
    powerLawExponentialMixture α t = (1 / t) ^ α := by
  unfold powerLawExponentialMixture
  unfold powerLawGammaDensity
  simp_rw [mul_assoc]
  change
    (∫ r : ℝ,
      (Real.Gamma α)⁻¹ *
        (r ^ (α - 1) * Real.exp (-(t * r)))
      ∂(MeasureTheory.volume.restrict (Set.Ioi 0))) =
      (1 / t) ^ α
  rw [MeasureTheory.integral_const_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hα ht]
  have hGamma : Real.Gamma α ≠ 0 :=
    (Real.Gamma_pos_of_pos hα).ne'
  field_simp
/-- The normalized power-law exponential mixture is strictly positive. -/
theorem powerLawExponentialMixture_positive
    {α t : ℝ}
    (hα : 0 < α)
    (ht : 0 < t) :
    0 < powerLawExponentialMixture α t := by
  rw [powerLawExponentialMixture_eq hα ht]
  exact Real.rpow_pos_of_pos (one_div_pos.mpr ht) α
/-- The normalized power-law exponential mixture is nonnegative. -/
theorem powerLawExponentialMixture_nonnegative
    {α t : ℝ}
    (hα : 0 < α)
    (ht : 0 < t) :
    0 ≤ powerLawExponentialMixture α t :=
  (powerLawExponentialMixture_positive hα ht).le
/--
A continuous family of nonnegative exponential-mode costs remains
nonnegative when integrated against the positive Gamma mixing density.
-/
theorem gammaWeightedContinuousModeCost_nonnegative
    {α : ℝ}
    (hα : 0 < α)
    (modeCost : ℝ → ℝ)
    (hMode : ∀ r, 0 ≤ modeCost r) :
    0 ≤
      ∫ r : ℝ in Set.Ioi 0,
        powerLawGammaDensity α r * modeCost r := by
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro r hr
  exact mul_nonneg
    (powerLawGammaDensity_nonnegative hα hr.le)
    (hMode r)
/--
Concrete power-law cost nonnegativity once the power-law cost is defined as
the Gamma-weighted integral of concrete nonnegative exponential-mode costs.
No separate Gamma-representation hypothesis is required.
-/
theorem concretePowerLawCost_nonnegative
    {α : ℝ}
    (hα : 0 < α)
    (exponentialModeCost : ℝ → ℝ)
    (hModes : ∀ r, 0 ≤ exponentialModeCost r) :
    0 ≤
      ∫ r : ℝ in Set.Ioi 0,
        powerLawGammaDensity α r * exponentialModeCost r :=
  gammaWeightedContinuousModeCost_nonnegative
    hα
    exponentialModeCost
    hModes
end CrossImpactNoPriceManipulation
