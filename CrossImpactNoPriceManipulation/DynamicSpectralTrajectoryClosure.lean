/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.DeterministicExponentialEnergy
import CrossImpactNoPriceManipulation.PositiveSpectralClosure
/-!
# Dynamic spectral trajectory closure
This file projects vector-valued exponential-memory trajectories onto the
orthonormal eigenbasis of a finite-dimensional positive operator.
It proves that every projected coordinate satisfies the corresponding scalar
exponential differential equation. It then obtains coordinate-work
nonnegativity from the verified scalar storage theorem and defines physical
mode work directly as the spectral eigenvalue-weighted coordinate sum.
-/
namespace CrossImpactNoPriceManipulation
section CoordinateDynamics
variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
/-- The scalar coordinate of a vector in a positive operator's eigenbasis. -/
noncomputable def positiveSpectralCoordinate
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (i : Fin n)
    (v : E) : ℝ :=
  inner ℝ ((hT.1.eigenvectorBasis hn) i) v
/--
Projection of a vector exponential-state equation onto a spectral coordinate
produces the scalar exponential-state equation.
-/
theorem positiveSpectralCoordinate_hasDerivAt
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (u x : ℝ → E)
    (ρ t : ℝ)
    (hx : HasDerivAt x (u t - ρ • x t) t)
    (i : Fin n) :
    HasDerivAt
      (fun s =>
        positiveSpectralCoordinate T hT n hn i (x s))
      (positiveSpectralCoordinate T hT n hn i (u t) -
        ρ * positiveSpectralCoordinate T hT n hn i (x t))
      t := by
  let coordinate : E →L[ℝ] ℝ :=
    InnerProductSpace.toDual ℝ E
      ((hT.1.eigenvectorBasis hn) i)
  have hconstant :
      HasDerivAt
        (fun _ : ℝ => coordinate)
        0
        t :=
    hasDerivAt_const t coordinate
  have hprojected := hconstant.clm_apply hx
  simpa [
    positiveSpectralCoordinate,
    coordinate,
    map_sub,
    map_smul,
    real_inner_comm
  ] using hprojected
/-- A zero vector initial state has zero value in every spectral coordinate. -/
theorem positiveSpectralCoordinate_initial_zero
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (x : ℝ → E)
    (a : ℝ)
    (hInitial : x a = 0)
    (i : Fin n) :
    positiveSpectralCoordinate T hT n hn i (x a) = 0 := by
  rw [hInitial]
  simp [positiveSpectralCoordinate]
/--
A projected scalar coordinate has nonnegative work whenever its work has the
verified storage-plus-nonnegative-decay representation.
-/
theorem positiveSpectralCoordinate_work_nonnegative
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (x : ℝ → E)
    (a b coordinateWork integratedDecay : ℝ)
    (i : Fin n)
    (hInitial : x a = 0)
    (hDecayNonnegative : 0 ≤ integratedDecay)
    (hEnergy :
      coordinateWork =
        scalarModeStorage
            (positiveSpectralCoordinate T hT n hn i (x b)) -
          scalarModeStorage
            (positiveSpectralCoordinate T hT n hn i (x a)) +
          integratedDecay) :
    0 ≤ coordinateWork := by
  apply scalarExponentialMode_work_nonnegative
    (fun t =>
      positiveSpectralCoordinate T hT n hn i (x t))
    (positiveSpectralCoordinate_initial_zero
      T hT n hn x a hInitial i)
    hDecayNonnegative
    hEnergy
end CoordinateDynamics
section DynamicPositiveModes
variable
    {κ : Type*}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
/--
The work of one positive operator mode is defined directly by its spectral
eigenvalue-weighted scalar coordinate works.
-/
noncomputable def positiveOperatorDynamicModeWork
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (coordinateWork : κ → Fin n → ℝ)
    (k : κ) : ℝ :=
  spectralModeWork
    Finset.univ
    ((hPositive k).1.eigenvalues hn)
    (coordinateWork k)
/--
Coordinate storage identities imply nonnegative work for one positive
operator mode, with no separate spectral-representation hypothesis.
-/
theorem positiveOperatorDynamicModeWork_nonnegative
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (x : κ → ℝ → E)
    (a b : ℝ)
    (coordinateWork integratedDecay : κ → Fin n → ℝ)
    (k : κ)
    (hInitial : x k a = 0)
    (hDecayNonnegative :
      ∀ i, 0 ≤ integratedDecay k i)
    (hEnergy :
      ∀ i,
        coordinateWork k i =
          scalarModeStorage
              (positiveSpectralCoordinate
                (operator k)
                (hPositive k)
                n
                hn
                i
                (x k b)) -
            scalarModeStorage
              (positiveSpectralCoordinate
                (operator k)
                (hPositive k)
                n
                hn
                i
                (x k a)) +
            integratedDecay k i) :
    0 ≤ positiveOperatorDynamicModeWork
      operator hPositive n hn coordinateWork k := by
  unfold positiveOperatorDynamicModeWork
  apply spectralModeWork_nonnegative
  · intro i _
    exact positiveOperator_eigenvalue_nonnegative
      (operator k) (hPositive k) n hn i
  · intro i _
    exact positiveSpectralCoordinate_work_nonnegative
      (operator k)
      (hPositive k)
      n
      hn
      (x k)
      a
      b
      (coordinateWork k i)
      (integratedDecay k i)
      i
      hInitial
      (hDecayNonnegative i)
      (hEnergy i)
/-- Total work of finitely many dynamic positive operator modes. -/
noncomputable def finiteDynamicPositiveMixtureWork
    (modes : Finset κ)
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (coordinateWork : κ → Fin n → ℝ) : ℝ :=
  ∑ k ∈ modes,
    positiveOperatorDynamicModeWork
      operator hPositive n hn coordinateWork k
/--
A finite mixture of positive dynamic modes has nonnegative work once every
projected coordinate has its scalar storage-and-decay identity.
-/
theorem finiteDynamicPositiveMixtureWork_nonnegative
    (modes : Finset κ)
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (x : κ → ℝ → E)
    (a b : ℝ)
    (coordinateWork integratedDecay : κ → Fin n → ℝ)
    (hInitial :
      ∀ k ∈ modes, x k a = 0)
    (hDecayNonnegative :
      ∀ k ∈ modes, ∀ i, 0 ≤ integratedDecay k i)
    (hEnergy :
      ∀ k ∈ modes, ∀ i,
        coordinateWork k i =
          scalarModeStorage
              (positiveSpectralCoordinate
                (operator k)
                (hPositive k)
                n
                hn
                i
                (x k b)) -
            scalarModeStorage
              (positiveSpectralCoordinate
                (operator k)
                (hPositive k)
                n
                hn
                i
                (x k a)) +
            integratedDecay k i) :
    0 ≤ finiteDynamicPositiveMixtureWork
      modes operator hPositive n hn coordinateWork := by
  unfold finiteDynamicPositiveMixtureWork
  apply Finset.sum_nonneg
  intro k hk
  exact positiveOperatorDynamicModeWork_nonnegative
    operator
    hPositive
    n
    hn
    x
    a
    b
    coordinateWork
    integratedDecay
    k
    (hInitial k hk)
    (hDecayNonnegative k hk)
    (hEnergy k hk)
/--
The dynamic finite positive-mode construction implies nonnegative expected
execution cost after adding passive state cost, instantaneous cost, and a
zero-mean unaffected-price term.
-/
theorem finiteDynamicPositiveMixture_financialNoPriceManipulation
    (modes : Finset κ)
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive : ∀ k, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (x : κ → ℝ → E)
    (a b : ℝ)
    (coordinateWork integratedDecay : κ → Fin n → ℝ)
    (hInitial :
      ∀ k ∈ modes, x k a = 0)
    (hDecayNonnegative :
      ∀ k ∈ modes, ∀ i, 0 ≤ integratedDecay k i)
    (hEnergy :
      ∀ k ∈ modes, ∀ i,
        coordinateWork k i =
          scalarModeStorage
              (positiveSpectralCoordinate
                (operator k)
                (hPositive k)
                n
                hn
                i
                (x k b)) -
            scalarModeStorage
              (positiveSpectralCoordinate
                (operator k)
                (hPositive k)
                n
                hn
                i
                (x k a)) +
            integratedDecay k i)
    {stateCost instantaneousCost expectedUnaffectedCost : ℝ}
    (hState : 0 ≤ stateCost)
    (hInstantaneous : 0 ≤ instantaneousCost)
    (hUnaffected : expectedUnaffectedCost = 0) :
    0 ≤ expectedExecutionCost
      expectedUnaffectedCost
      (totalImpactCost
        (finiteDynamicPositiveMixtureWork
          modes operator hPositive n hn coordinateWork)
        stateCost
        instantaneousCost) := by
  apply expectedExecutionCost_nonnegative hUnaffected
  apply totalImpactCost_nonnegative
  · exact finiteDynamicPositiveMixtureWork_nonnegative
      modes
      operator
      hPositive
      n
      hn
      x
      a
      b
      coordinateWork
      integratedDecay
      hInitial
      hDecayNonnegative
      hEnergy
  · exact hState
  · exact hInstantaneous
end DynamicPositiveModes
end CrossImpactNoPriceManipulation
