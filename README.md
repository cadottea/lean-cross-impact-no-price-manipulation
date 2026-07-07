# Lean Verification of Cross-Impact No-Price-Manipulation

This repository contains a machine-checked Lean 4 development of

no-price-manipulation results for a cross-impact market model.

## Main results

- Exact round-trip criterion for the formalized linear stage.

- Exact necessary-and-sufficient linear no-price-manipulation criterion.

- Nonnegative work for positive exponential operator modes.

- Closure under finite positive exponential mixtures.

- Exact Gamma/Laplace representation of a power-law kernel.

- Nonnegative concrete continuous power-law impact work.

- Deterministic finite-step martingale bridge.

- Random finite-step predictable-strategy martingale bridge.

- Constructive negative-round-trip converse for the linear criterion.

## Final predictable-strategy theorem

The principal final declaration is:

concreteContinuousPowerLaw_predictableNoPriceManipulation

It combines zero expected unaffected-price cost for a random finite-step

predictable strategy with the verified nonnegative continuous power-law

impact contribution.

## Verified state

- Complete Lake build: passed.

- Build jobs: 8,597.

- Compiler and linter warnings: 0.

- Audited Lean source files: 17.

- Expected public declarations reconciled: 17 of 17.

- sorry declarations: 0.

- admit declarations: 0.

- Custom axioms: 0.

- opaque declarations: 0.

- Custom constants: 0.

The complete reconciliation report is located at:

docs/proof_log_to_lean_reconciliation.md

## Build

Install Lean using elan and run:

    lake build

To compile the final predictable bridge directly:

    lake env lean CrossImpactNoPriceManipulation/PredictableMartingaleBridge.lean

## Scope

The sufficient theorem covers random finite-step predictable strategies with:

- strategy coefficients measurable relative to the corresponding information;

- integrable price increments;

- conditionally mean-zero increments;

- integrable strategy-times-increment products;

- the stated positivity and analytic assumptions for the continuous

  power-law impact model.

The exact converse applies to the formalized linear model.

## Explicit nonclaims

This repository does not claim:

- a general continuous-time stochastic integral;

- semimartingale or Ito integration;

- a nonlinear power-law converse;

- automatic proof of every analytic or integrability hypothesis.

## License

Apache License 2.0.

