/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import CrossImpactNoPriceManipulation.DeterministicMartingaleBridge
import CrossImpactNoPriceManipulation.ExactLinearStage
/-!
# Converse negative-cost round-trip theorem
This file proves the converse direction for the exact linear criterion:
failure of compressed positivity produces an explicit round-trip direction
with strictly negative quadratic impact cost.
-/
namespace CrossImpactNoPriceManipulation
/--
Failure of nonnegativity of the compressed quadratic form yields a vector
whose projected round-trip direction has strictly negative cost.
-/
theorem exists_negative_compressed_witness
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (totalFlow : E →L[ℝ] ℝ)
    [(roundTripSubspace totalFlow).HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hFailure :
      ¬ ∀ x,
        0 ≤ compressedQuadraticCost
          (roundTripSubspace totalFlow) S x) :
    ∃ x,
      compressedQuadraticCost
        (roundTripSubspace totalFlow) S x < 0 := by
  simpa only [not_le] using (not_forall.mp hFailure)
/--
Failure of compressed positivity produces an explicit round-trip strategy
with strictly negative quadratic cost.
-/
theorem exists_negativeCost_roundTrip_of_compressed_failure
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (totalFlow : E →L[ℝ] ℝ)
    [(roundTripSubspace totalFlow).HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hFailure :
      ¬ ∀ x,
        0 ≤ compressedQuadraticCost
          (roundTripSubspace totalFlow) S x) :
    ∃ u,
      totalFlow u = 0 ∧
      quadraticCost S u < 0 := by
  obtain ⟨x, hx⟩ :=
    exists_negative_compressed_witness
      totalFlow S hFailure
  refine ⟨(roundTripSubspace totalFlow).starProjection x, ?_, ?_⟩
  · exact
      (mem_roundTripSubspace_iff
        totalFlow
        ((roundTripSubspace totalFlow).starProjection x)).mp
        ((roundTripSubspace totalFlow).starProjection_apply_mem x)
  · simpa [compressedQuadraticCost] using hx
/--
Converse theorem for the symmetrized linear impact operator: if the exact
compressed positivity condition fails, then there exists a round trip with
strictly negative symmetrized impact cost.
-/
theorem exists_priceManipulation_of_linearCriterion_failure
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (totalFlow : E →L[ℝ] ℝ)
    [(roundTripSubspace totalFlow).HasOrthogonalProjection]
    (K : E →L[ℝ] E)
    (hFailure :
      ¬ ∀ x,
        0 ≤ compressedQuadraticCost
          (roundTripSubspace totalFlow)
          (symmetrizedOperator K)
          x) :
    ∃ u,
      totalFlow u = 0 ∧
      quadraticCost (symmetrizedOperator K) u < 0 :=
  exists_negativeCost_roundTrip_of_compressed_failure
    totalFlow
    (symmetrizedOperator K)
    hFailure
/--
Exact converse formulation: absence of a negative-cost round trip is
equivalent to compressed positivity of the symmetrized impact operator.
-/
theorem no_negative_roundTrip_iff_compressed_positive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (totalFlow : E →L[ℝ] ℝ)
    [(roundTripSubspace totalFlow).HasOrthogonalProjection]
    (K : E →L[ℝ] E) :
    (¬ ∃ u,
      totalFlow u = 0 ∧
      quadraticCost (symmetrizedOperator K) u < 0) ↔
    ∀ x,
      0 ≤ compressedQuadraticCost
        (roundTripSubspace totalFlow)
        (symmetrizedOperator K)
        x := by
  constructor
  · intro hNoNegative
    by_contra hFailure
    exact hNoNegative
      (exists_priceManipulation_of_linearCriterion_failure
        totalFlow K hFailure)
  · intro hPositive hNegative
    obtain ⟨u, huRoundTrip, huNegative⟩ := hNegative
    have hRoundTripNonnegative :
        0 ≤ quadraticCost (symmetrizedOperator K) u :=
      (exact_linear_noPriceManipulation_iff totalFlow K).mpr
        hPositive
        u
        huRoundTrip
    exact (not_lt_of_ge hRoundTripNonnegative) huNegative
end CrossImpactNoPriceManipulation
