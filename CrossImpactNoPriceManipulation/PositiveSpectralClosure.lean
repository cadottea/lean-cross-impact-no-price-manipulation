/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import CrossImpactNoPriceManipulation.FiniteSpectralMixtureEnergy
/-!
# Positive finite-dimensional spectral closure
This file removes the previously explicit nonnegative-eigenvalue hypothesis for
finite-dimensional positive operators.
For a positive linear operator on a finite-dimensional real inner-product
space, mathlib's spectral theorem supplies an orthonormal eigenbasis. Positivity
then forces every eigenvalue to be nonnegative. The operator acts diagonally in
that basis, so nonnegative scalar coordinate works imply nonnegative physical
matrix-mode work through the verified spectral-mixture theorem.
The remaining boundary is dynamic: coordinate work must still be instantiated
from projected time-dependent exponential-state trajectories.
-/
namespace CrossImpactNoPriceManipulation
section PositiveOperatorSpectrum
variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
/--
Every eigenvalue in the orthonormal spectral basis of a positive
finite-dimensional real operator is nonnegative.
-/
theorem positiveOperator_eigenvalue_nonnegative
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (i : Fin n) :
    0 ≤ hT.1.eigenvalues hn i := by
  have hpos :
      0 ≤ inner ℝ
        (T ((hT.1.eigenvectorBasis hn) i))
        ((hT.1.eigenvectorBasis hn) i) :=
    hT.2 ((hT.1.eigenvectorBasis hn) i)
  rw [
    hT.1.apply_eigenvectorBasis hn i,
    real_inner_smul_left,
    real_inner_self_eq_norm_sq,
    (hT.1.eigenvectorBasis hn).norm_eq_one i
  ] at hpos
  simpa using hpos
/--
A positive operator acts coordinatewise in its orthonormal eigenbasis by
multiplication with its nonnegative real eigenvalues.
-/
theorem positiveOperator_spectralCoordinateAction
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (v : E)
    (i : Fin n) :
    ((hT.1.eigenvectorBasis hn).repr (T v)).ofLp i =
      hT.1.eigenvalues hn i *
        ((hT.1.eigenvectorBasis hn).repr v).ofLp i := by
  simpa using
    hT.1.eigenvectorBasis_apply_self_apply hn v i
/--
The spectral eigenvalues of a positive operator satisfy the exact
nonnegativity interface required by the finite spectral-mode theorem.
-/
theorem positiveOperator_spectralWeights_nonnegative
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n) :
    ∀ i ∈ Finset.univ,
      0 ≤ hT.1.eigenvalues hn i := by
  intro i _
  exact positiveOperator_eigenvalue_nonnegative T hT n hn i
/--
A positive finite-dimensional operator has nonnegative represented mode work
whenever each scalar spectral-coordinate work is nonnegative and the physical
work equals the spectral eigenvalue-weighted sum.
-/
theorem positiveOperator_modeWork_nonnegative
    (T : E →ₗ[ℝ] E)
    (hT : T.IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (coordinateWork : Fin n → ℝ)
    (modeWork : ℝ)
    (hCoordinateWork :
      ∀ i ∈ Finset.univ, 0 ≤ coordinateWork i)
    (hRepresentation :
      modeWork =
        spectralModeWork
          Finset.univ
          (hT.1.eigenvalues hn)
          coordinateWork) :
    0 ≤ modeWork := by
  exact matrixModeWork_nonnegative_of_spectralRepresentation
    Finset.univ
    (hT.1.eigenvalues hn)
    coordinateWork
    modeWork
    hRepresentation
    (positiveOperator_spectralWeights_nonnegative T hT n hn)
    hCoordinateWork
end PositiveOperatorSpectrum
section FinitePositiveOperatorModes
variable
    {κ : Type*}
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
/--
A finite family of positive operators has nonnegative aggregate memory work
when every scalar spectral-coordinate work is nonnegative and every physical
mode work has its exact spectral representation.
-/
theorem finitePositiveOperatorMixtureWork_nonnegative
    (modes : Finset κ)
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive :
      ∀ k ∈ modes, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (coordinateWork : κ → Fin n → ℝ)
    (modeWork : κ → ℝ)
    (hCoordinateWork :
      ∀ k ∈ modes, ∀ i ∈ Finset.univ,
        0 ≤ coordinateWork k i)
    (hRepresentation :
      ∀ k, ∀ hk : k ∈ modes,
        modeWork k =
          spectralModeWork
            Finset.univ
            ((hPositive k hk).1.eigenvalues hn)
            (coordinateWork k)) :
    0 ≤ finiteSpectralMixtureWork modes modeWork := by
  apply finiteSpectralMixtureWork_nonnegative
  intro k hk
  exact positiveOperator_modeWork_nonnegative
    (operator k)
    (hPositive k hk)
    n
    hn
    (coordinateWork k)
    (modeWork k)
    (hCoordinateWork k hk)
    (hRepresentation k hk)
/--
Concrete financial no-price-manipulation consequence for a finite family of
positive operator modes, subject only to scalar-coordinate work nonnegativity
and exact spectral work representation.
-/
theorem finitePositiveOperatorMixture_financialNoPriceManipulation
    (modes : Finset κ)
    (operator : κ → E →ₗ[ℝ] E)
    (hPositive :
      ∀ k ∈ modes, (operator k).IsPositive)
    (n : ℕ)
    (hn : Module.finrank ℝ E = n)
    (coordinateWork : κ → Fin n → ℝ)
    (modeWork : κ → ℝ)
    (hCoordinateWork :
      ∀ k ∈ modes, ∀ i ∈ Finset.univ,
        0 ≤ coordinateWork k i)
    (hRepresentation :
      ∀ k, ∀ hk : k ∈ modes,
        modeWork k =
          spectralModeWork
            Finset.univ
            ((hPositive k hk).1.eigenvalues hn)
            (coordinateWork k))
    {stateCost instantaneousCost expectedUnaffectedCost : ℝ}
    (hState : 0 ≤ stateCost)
    (hInstantaneous : 0 ≤ instantaneousCost)
    (hUnaffected : expectedUnaffectedCost = 0) :
    0 ≤ expectedExecutionCost
      expectedUnaffectedCost
      (totalImpactCost
        (finiteSpectralMixtureWork modes modeWork)
        stateCost
        instantaneousCost) := by
  apply expectedExecutionCost_nonnegative hUnaffected
  apply totalImpactCost_nonnegative
  · exact finitePositiveOperatorMixtureWork_nonnegative
      modes
      operator
      hPositive
      n
      hn
      coordinateWork
      modeWork
      hCoordinateWork
      hRepresentation
  · exact hState
  · exact hInstantaneous
end FinitePositiveOperatorModes
end CrossImpactNoPriceManipulation
