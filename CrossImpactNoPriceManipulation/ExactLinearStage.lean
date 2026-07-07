/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib
import CrossImpactNoPriceManipulation.LinearCriterion
/-!
# Exact linear no-price-manipulation criterion
This file formalizes the exact Hilbert-space criterion for a linear impact
operator restricted to the zero-total-flow trading-rate subspace.
A continuous linear map `totalFlow` represents integration of a trading rate
over the execution horizon. Its kernel is therefore the abstract round-trip
subspace.
The orthogonal projection onto that kernel is used to state the exact
compressed-operator positivity criterion.
-/
namespace CrossImpactNoPriceManipulation
section RoundTripSubspace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The abstract total-flow map. Its kernel consists of inventory round trips. -/
def roundTripSubspace (totalFlow : E →L[ℝ] ℝ) : Submodule ℝ E :=
  totalFlow.ker
/-- A trading rate is a round trip precisely when its total flow is zero. -/
theorem mem_roundTripSubspace_iff
    (totalFlow : E →L[ℝ] ℝ)
    (u : E) :
    u ∈ roundTripSubspace totalFlow ↔ totalFlow u = 0 := by
  rfl
end RoundTripSubspace
section ProjectionCriterion
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/--
The star projection onto a subspace is idempotent in the elementary sense used
by the abstract projection theorem.
-/
theorem starProjection_isIdempotent
    (U : Submodule ℝ E)
    [U.HasOrthogonalProjection] :
    IsIdempotent U.starProjection := by
  intro x
  have hx : U.starProjection x ∈ U :=
    U.starProjection_apply_mem x
  exact U.starProjection_eq_self_iff.mpr hx
/--
Nonnegativity of a quadratic cost on a subspace is equivalent to nonnegativity
after orthogonally projecting every vector onto that subspace.
-/
theorem quadratic_nonnegative_on_subspace_iff_compressed
    (U : Submodule ℝ E)
    [U.HasOrthogonalProjection]
    (S : E →L[ℝ] E) :
    (∀ u, u ∈ U → 0 ≤ quadraticCost S u) ↔
      ∀ x, 0 ≤ quadraticCost S (U.starProjection x) := by
  rw [← quadratic_nonnegative_on_fixedPoints_iff_after_projection
    U.starProjection S (starProjection_isIdempotent U)]
  constructor
  · intro h u hu
    exact h u (U.starProjection_eq_self_iff.mp hu)
  · intro h u hu
    exact h u (U.starProjection_eq_self_iff.mpr hu)
/-- The quadratic form of `S` compressed to the subspace `U`. -/
noncomputable def compressedQuadraticCost
    (U : Submodule ℝ E)
    [U.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (x : E) : ℝ :=
  quadraticCost S (U.starProjection x)
/--
Exact necessary-and-sufficient positivity criterion for the quadratic cost on
the abstract round-trip subspace.
-/
theorem exact_roundTrip_criterion
    (totalFlow : E →L[ℝ] ℝ)
    [(roundTripSubspace totalFlow).HasOrthogonalProjection]
    (S : E →L[ℝ] E) :
    (∀ u, totalFlow u = 0 → 0 ≤ quadraticCost S u) ↔
      ∀ x, 0 ≤ compressedQuadraticCost
        (roundTripSubspace totalFlow) S x := by
  simpa [
    compressedQuadraticCost,
    mem_roundTripSubspace_iff
  ] using
    quadratic_nonnegative_on_subspace_iff_compressed
      (roundTripSubspace totalFlow) S
end ProjectionCriterion
section SymmetrizedOperator
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- The self-adjoint symmetrization `(K + K†) / 2` of a linear impact operator. -/
noncomputable def symmetrizedOperator
    (K : E →L[ℝ] E) : E →L[ℝ] E :=
  (2 : ℝ)⁻¹ • (K + K.adjoint)
/--
The exact linear no-price-manipulation criterion, stated for the symmetrized
impact operator and the zero-total-flow round-trip subspace.
-/
theorem exact_linear_noPriceManipulation_iff
    (totalFlow : E →L[ℝ] ℝ)
    [(roundTripSubspace totalFlow).HasOrthogonalProjection]
    (K : E →L[ℝ] E) :
    (∀ u, totalFlow u = 0 →
      0 ≤ quadraticCost (symmetrizedOperator K) u) ↔
    ∀ x,
      0 ≤ compressedQuadraticCost
        (roundTripSubspace totalFlow)
        (symmetrizedOperator K)
        x :=
  exact_roundTrip_criterion totalFlow (symmetrizedOperator K)
end SymmetrizedOperator
end CrossImpactNoPriceManipulation
