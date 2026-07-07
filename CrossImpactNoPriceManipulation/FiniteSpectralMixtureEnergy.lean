/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.DeterministicExponentialEnergy

/-!
# Finite spectral exponential-mixture energy

This file lifts the verified scalar exponential-mode positivity result to
finite spectral coordinates with nonnegative eigenvalues and then to a
finite family of exponential-memory modes.
-/

namespace CrossImpactNoPriceManipulation

section SpectralCoordinates

variable {ι : Type*}

/--
The work of a diagonal positive-semidefinite mode is the eigenvalue-weighted
sum of its scalar coordinate works.
-/
def spectralModeWork
    (coordinates : Finset ι)
    (eigenvalue coordinateWork : ι → ℝ) : ℝ :=
  ∑ i ∈ coordinates, eigenvalue i * coordinateWork i

/--
Nonnegative eigenvalues and nonnegative scalar coordinate works imply
nonnegative work for the diagonal positive-semidefinite mode.
-/
theorem spectralModeWork_nonnegative
    (coordinates : Finset ι)
    (eigenvalue coordinateWork : ι → ℝ)
    (hEigenvalue : ∀ i ∈ coordinates, 0 ≤ eigenvalue i)
    (hCoordinateWork : ∀ i ∈ coordinates, 0 ≤ coordinateWork i) :
    0 ≤ spectralModeWork coordinates eigenvalue coordinateWork := by
  unfold spectralModeWork
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (hEigenvalue i hi)
    (hCoordinateWork i hi)

/--
Transfer the spectral-coordinate result through an exact representation of
the physical matrix-mode work.
-/
theorem matrixModeWork_nonnegative_of_spectralRepresentation
    (coordinates : Finset ι)
    (eigenvalue coordinateWork : ι → ℝ)
    (matrixModeWork : ℝ)
    (hRepresentation :
      matrixModeWork =
        spectralModeWork coordinates eigenvalue coordinateWork)
    (hEigenvalue : ∀ i ∈ coordinates, 0 ≤ eigenvalue i)
    (hCoordinateWork : ∀ i ∈ coordinates, 0 ≤ coordinateWork i) :
    0 ≤ matrixModeWork := by
  rw [hRepresentation]
  exact spectralModeWork_nonnegative
    coordinates
    eigenvalue
    coordinateWork
    hEigenvalue
    hCoordinateWork

end SpectralCoordinates

section FiniteMemoryModes

variable {ι κ : Type*}

/-- The total memory work of finitely many exponential modes. -/
def finiteSpectralMixtureWork
    (modes : Finset κ)
    (modeWork : κ → ℝ) : ℝ :=
  ∑ k ∈ modes, modeWork k

/-- A finite sum of nonnegative exponential-mode works is nonnegative. -/
theorem finiteSpectralMixtureWork_nonnegative
    (modes : Finset κ)
    (modeWork : κ → ℝ)
    (hModeWork : ∀ k ∈ modes, 0 ≤ modeWork k) :
    0 ≤ finiteSpectralMixtureWork modes modeWork := by
  unfold finiteSpectralMixtureWork
  apply Finset.sum_nonneg
  intro k hk
  exact hModeWork k hk

/--
A finite family of spectrally represented positive-semidefinite modes has
nonnegative total memory work.
-/
theorem finitePSDExponentialMixtureWork_nonnegative
    (modes : Finset κ)
    (coordinates : κ → Finset ι)
    (eigenvalue coordinateWork : κ → ι → ℝ)
    (modeWork : κ → ℝ)
    (hRepresentation :
      ∀ k ∈ modes,
        modeWork k =
          spectralModeWork
            (coordinates k)
            (eigenvalue k)
            (coordinateWork k))
    (hEigenvalue :
      ∀ k ∈ modes, ∀ i ∈ coordinates k,
        0 ≤ eigenvalue k i)
    (hCoordinateWork :
      ∀ k ∈ modes, ∀ i ∈ coordinates k,
        0 ≤ coordinateWork k i) :
    0 ≤ finiteSpectralMixtureWork modes modeWork := by
  apply finiteSpectralMixtureWork_nonnegative
  intro k hk
  exact matrixModeWork_nonnegative_of_spectralRepresentation
    (coordinates k)
    (eigenvalue k)
    (coordinateWork k)
    (modeWork k)
    (hRepresentation k hk)
    (hEigenvalue k hk)
    (hCoordinateWork k hk)

/--
Finite positive-semidefinite exponential-memory modes combine with passive
state cost, instantaneous cost, and a zero-mean unaffected-price term to
give nonnegative expected execution cost.
-/
theorem finitePSDExponentialMixture_financialNoPriceManipulation
    (modes : Finset κ)
    (modeWork : κ → ℝ)
    {stateCost instantaneousCost expectedUnaffectedCost : ℝ}
    (hModeWork : ∀ k ∈ modes, 0 ≤ modeWork k)
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
  · exact finiteSpectralMixtureWork_nonnegative
      modes modeWork hModeWork
  · exact hState
  · exact hInstantaneous

end FiniteMemoryModes

end CrossImpactNoPriceManipulation
