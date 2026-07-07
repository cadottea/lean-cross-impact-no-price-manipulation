/-
Copyright (c) 2026 Andrew Cadotte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Cadotte
-/
import Mathlib

/-!
# Exact abstract round-trip positivity criterion

This file proves the first logical component of the no-price-manipulation
formalization.

For an idempotent map `P`, nonnegativity of a cost on the fixed-point set of
`P` is equivalent to nonnegativity of the cost after applying `P` to every
input.
-/

namespace CrossImpactNoPriceManipulation

/-- A map is idempotent when applying it twice equals applying it once. -/
def IsIdempotent {E : Type*} (P : E → E) : Prop :=
  ∀ x, P (P x) = P x

/--
Nonnegativity on all fixed points is equivalent to nonnegativity after
projection.
-/
theorem nonnegative_on_fixedPoints_iff_after_projection
    {E : Type*}
    (P : E → E)
    (cost : E → ℝ)
    (hP : IsIdempotent P) :
    (∀ y, P y = y → 0 ≤ cost y) ↔
      ∀ x, 0 ≤ cost (P x) := by
  constructor
  · intro h x
    exact h (P x) (hP x)
  · intro h y hy
    simpa [hy] using h y

section QuadraticCost

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic cost associated with a continuous linear operator. -/
def quadraticCost (S : E →L[ℝ] E) (x : E) : ℝ :=
  inner ℝ x (S x)

/--
Specialization of the projection criterion to the quadratic cost generated
by a continuous linear operator.
-/
theorem quadratic_nonnegative_on_fixedPoints_iff_after_projection
    (P : E → E)
    (S : E →L[ℝ] E)
    (hP : IsIdempotent P) :
    (∀ y, P y = y → 0 ≤ quadraticCost S y) ↔
      ∀ x, 0 ≤ quadraticCost S (P x) :=
  nonnegative_on_fixedPoints_iff_after_projection
    P (quadraticCost S) hP

end QuadraticCost

end CrossImpactNoPriceManipulation
