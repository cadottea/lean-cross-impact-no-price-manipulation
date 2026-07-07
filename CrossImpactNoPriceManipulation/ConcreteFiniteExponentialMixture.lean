/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.ScalarWorkIntegralClosure
/-!
# Concrete finite-dimensional exponential mixture
This file defines every spectral-coordinate work directly as its interval
integral. It then proves nonnegative work for each positive operator mode,
for a finite mixture of modes, and for the resulting expected execution cost.
No abstract coordinate-work, energy-representation, or spectral-representation
hypothesis remains.
-/
namespace CrossImpactNoPriceManipulation
section ConcreteCoordinateWork
variable
    {κ E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
/-- Concrete work integral for one mode and one spectral coordinate. -/
noncomputable def concreteSpectralCoordinateWork
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : κ → ℝ → E)
    (a b : ℝ)
    (k : κ)
    (i : Fin n) : ℝ :=
  ∫ t in a..b,
    positiveSpectralCoordinate
        (operator k) (hPositive k) n hn i (u k t) *
      positiveSpectralCoordinate
        (operator k) (hPositive k) n hn i (x k t)
/--
Every concrete coordinate work is nonnegative under the vector exponential
state equation, zero initial state, nonnegative decay rate, and the required
continuity and integrability assumptions.
-/
theorem concreteSpectralCoordinateWork_nonnegative
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : κ → ℝ → E)
    (a b : ℝ)
    (ρ : κ → ℝ)
    (k : κ)
    (i : Fin n)
    (hab : a ≤ b)
    (hρ : 0 ≤ ρ k)
    (hInitial : x k a = 0)
    (hCoordinateContinuous :
      ContinuousOn
        (fun t =>
          positiveSpectralCoordinate
            (operator k) (hPositive k) n hn i (x k t))
        (Set.uIcc a b))
    (hVectorODE :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivAt
          (x k)
          (u k t - ρ k • x k t)
          t)
    (hDerivativeIntegrable :
      IntervalIntegrable
        (fun t =>
          positiveSpectralCoordinate
              (operator k) (hPositive k) n hn i (u k t) -
            ρ k *
              positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (x k t))
        MeasureTheory.volume
        a
        b)
    (hPairingIntegrable :
      IntervalIntegrable
        (fun t =>
          ((positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (u k t) -
              ρ k *
                positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (x k t)) *
            positiveSpectralCoordinate
              (operator k) (hPositive k) n hn i (x k t)) +
          (positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (x k t) *
            (positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (u k t) -
              ρ k *
                positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (x k t))))
        MeasureTheory.volume
        a
        b)
    (hDecayIntegrable :
      IntervalIntegrable
        (fun t =>
          ρ k *
            positiveSpectralCoordinate
              (operator k) (hPositive k) n hn i (x k t) ^ 2)
        MeasureTheory.volume
        a
        b) :
    0 ≤ concreteSpectralCoordinateWork
      operator hPositive n hn u x a b k i := by
  unfold concreteSpectralCoordinateWork
  exact positiveSpectralCoordinate_workIntegral_nonnegative
    (operator k)
    (hPositive k)
    n
    hn
    (u k)
    (x k)
    a
    b
    (ρ k)
    i
    hab
    hρ
    hInitial
    hCoordinateContinuous
    hVectorODE
    hDerivativeIntegrable
    hPairingIntegrable
    hDecayIntegrable
end ConcreteCoordinateWork
section ConcreteModeAndMixture
variable
    {κ E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
/-- Concrete work of one positive exponential-memory operator mode. -/
noncomputable def concretePositiveOperatorModeWork
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : κ → ℝ → E)
    (a b : ℝ)
    (k : κ) : ℝ :=
  positiveOperatorDynamicModeWork
    operator
    hPositive
    n
    hn
    (concreteSpectralCoordinateWork
      operator hPositive n hn u x a b)
    k
/--
Concrete positive-operator mode work is nonnegative, with coordinate work
defined directly by interval integrals.
-/
theorem concretePositiveOperatorModeWork_nonnegative
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : κ → ℝ → E)
    (a b : ℝ)
    (ρ : κ → ℝ)
    (k : κ)
    (hab : a ≤ b)
    (hρ : 0 ≤ ρ k)
    (hInitial : x k a = 0)
    (hCoordinateContinuous :
      ∀ i,
        ContinuousOn
          (fun t =>
            positiveSpectralCoordinate
              (operator k) (hPositive k) n hn i (x k t))
          (Set.uIcc a b))
    (hVectorODE :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivAt
          (x k)
          (u k t - ρ k • x k t)
          t)
    (hDerivativeIntegrable :
      ∀ i,
        IntervalIntegrable
          (fun t =>
            positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (u k t) -
              ρ k *
                positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (x k t))
          MeasureTheory.volume
          a
          b)
    (hPairingIntegrable :
      ∀ i,
        IntervalIntegrable
          (fun t =>
            ((positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (u k t) -
                ρ k *
                  positiveSpectralCoordinate
                    (operator k) (hPositive k) n hn i (x k t)) *
              positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (x k t)) +
            (positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (x k t) *
              (positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (u k t) -
                ρ k *
                  positiveSpectralCoordinate
                    (operator k) (hPositive k) n hn i (x k t))))
          MeasureTheory.volume
          a
          b)
    (hDecayIntegrable :
      ∀ i,
        IntervalIntegrable
          (fun t =>
            ρ k *
              positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (x k t) ^ 2)
          MeasureTheory.volume
          a
          b) :
    0 ≤ concretePositiveOperatorModeWork
      operator hPositive n hn u x a b k := by
  unfold concretePositiveOperatorModeWork
  unfold positiveOperatorDynamicModeWork
  apply spectralModeWork_nonnegative
  · intro i _
    exact positiveOperator_eigenvalue_nonnegative
      (operator k)
      (hPositive k)
      n
      hn
      i
  · intro i _
    exact concreteSpectralCoordinateWork_nonnegative
      operator
      hPositive
      n
      hn
      u
      x
      a
      b
      ρ
      k
      i
      hab
      hρ
      hInitial
      (hCoordinateContinuous i)
      hVectorODE
      (hDerivativeIntegrable i)
      (hPairingIntegrable i)
      (hDecayIntegrable i)
/-- Concrete total work of finitely many exponential-memory modes. -/
noncomputable def concreteFiniteExponentialMixtureWork
    (modes : Finset κ)
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : κ → ℝ → E)
    (a b : ℝ) : ℝ :=
  ∑ k ∈ modes,
    concretePositiveOperatorModeWork
      operator hPositive n hn u x a b k
/--
The concrete finite-dimensional exponential-memory mixture has nonnegative
work.
-/
theorem concreteFiniteExponentialMixtureWork_nonnegative
    (modes : Finset κ)
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : κ → ℝ → E)
    (a b : ℝ)
    (ρ : κ → ℝ)
    (hab : a ≤ b)
    (hρ : ∀ k ∈ modes, 0 ≤ ρ k)
    (hInitial : ∀ k ∈ modes, x k a = 0)
    (hCoordinateContinuous :
      ∀ k ∈ modes, ∀ i,
        ContinuousOn
          (fun t =>
            positiveSpectralCoordinate
              (operator k) (hPositive k) n hn i (x k t))
          (Set.uIcc a b))
    (hVectorODE :
      ∀ k ∈ modes,
        ∀ t ∈ Set.Ioo (min a b) (max a b),
          HasDerivAt
            (x k)
            (u k t - ρ k • x k t)
            t)
    (hDerivativeIntegrable :
      ∀ k ∈ modes, ∀ i,
        IntervalIntegrable
          (fun t =>
            positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (u k t) -
              ρ k *
                positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (x k t))
          MeasureTheory.volume
          a
          b)
    (hPairingIntegrable :
      ∀ k ∈ modes, ∀ i,
        IntervalIntegrable
          (fun t =>
            ((positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (u k t) -
                ρ k *
                  positiveSpectralCoordinate
                    (operator k) (hPositive k) n hn i (x k t)) *
              positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (x k t)) +
            (positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (x k t) *
              (positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (u k t) -
                ρ k *
                  positiveSpectralCoordinate
                    (operator k) (hPositive k) n hn i (x k t))))
          MeasureTheory.volume
          a
          b)
    (hDecayIntegrable :
      ∀ k ∈ modes, ∀ i,
        IntervalIntegrable
          (fun t =>
            ρ k *
              positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (x k t) ^ 2)
          MeasureTheory.volume
          a
          b) :
    0 ≤ concreteFiniteExponentialMixtureWork
      modes operator hPositive n hn u x a b := by
  unfold concreteFiniteExponentialMixtureWork
  apply Finset.sum_nonneg
  intro k hk
  exact concretePositiveOperatorModeWork_nonnegative
    operator
    hPositive
    n
    hn
    u
    x
    a
    b
    ρ
    k
    hab
    (hρ k hk)
    (hInitial k hk)
    (hCoordinateContinuous k hk)
    (hVectorODE k hk)
    (hDerivativeIntegrable k hk)
    (hPairingIntegrable k hk)
    (hDecayIntegrable k hk)
/--
Concrete deterministic finite-dimensional exponential-mixture
no-price-manipulation theorem.
-/
theorem concreteFiniteExponentialMixture_financialNoPriceManipulation
    (modes : Finset κ)
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : κ → ℝ → E)
    (a b : ℝ)
    (ρ : κ → ℝ)
    (hab : a ≤ b)
    (hρ : ∀ k ∈ modes, 0 ≤ ρ k)
    (hInitial : ∀ k ∈ modes, x k a = 0)
    (hCoordinateContinuous :
      ∀ k ∈ modes, ∀ i,
        ContinuousOn
          (fun t =>
            positiveSpectralCoordinate
              (operator k) (hPositive k) n hn i (x k t))
          (Set.uIcc a b))
    (hVectorODE :
      ∀ k ∈ modes,
        ∀ t ∈ Set.Ioo (min a b) (max a b),
          HasDerivAt
            (x k)
            (u k t - ρ k • x k t)
            t)
    (hDerivativeIntegrable :
      ∀ k ∈ modes, ∀ i,
        IntervalIntegrable
          (fun t =>
            positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (u k t) -
              ρ k *
                positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (x k t))
          MeasureTheory.volume
          a
          b)
    (hPairingIntegrable :
      ∀ k ∈ modes, ∀ i,
        IntervalIntegrable
          (fun t =>
            ((positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (u k t) -
                ρ k *
                  positiveSpectralCoordinate
                    (operator k) (hPositive k) n hn i (x k t)) *
              positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (x k t)) +
            (positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (x k t) *
              (positiveSpectralCoordinate
                  (operator k) (hPositive k) n hn i (u k t) -
                ρ k *
                  positiveSpectralCoordinate
                    (operator k) (hPositive k) n hn i (x k t))))
          MeasureTheory.volume
          a
          b)
    (hDecayIntegrable :
      ∀ k ∈ modes, ∀ i,
        IntervalIntegrable
          (fun t =>
            ρ k *
              positiveSpectralCoordinate
                (operator k) (hPositive k) n hn i (x k t) ^ 2)
          MeasureTheory.volume
          a
          b)
    {stateCost instantaneousCost expectedUnaffectedCost : ℝ}
    (hState : 0 ≤ stateCost)
    (hInstantaneous : 0 ≤ instantaneousCost)
    (hUnaffected : expectedUnaffectedCost = 0) :
    0 ≤ expectedExecutionCost
      expectedUnaffectedCost
      (totalImpactCost
        (concreteFiniteExponentialMixtureWork
          modes operator hPositive n hn u x a b)
        stateCost
        instantaneousCost) := by
  apply expectedExecutionCost_nonnegative hUnaffected
  apply totalImpactCost_nonnegative
  · exact concreteFiniteExponentialMixtureWork_nonnegative
      modes
      operator
      hPositive
      n
      hn
      u
      x
      a
      b
      ρ
      hab
      hρ
      hInitial
      hCoordinateContinuous
      hVectorODE
      hDerivativeIntegrable
      hPairingIntegrable
      hDecayIntegrable
  · exact hState
  · exact hInstantaneous
end ConcreteModeAndMixture
end CrossImpactNoPriceManipulation
