# Lean Verification of Cross-Impact No-Price-Manipulation

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21250432.svg)](https://doi.org/10.5281/zenodo.21250432)

This repository contains a machine-checked Lean 4 development of

no-price-manipulation results for a cross-impact market model.

The central economic question is simple:

> Can a trader begin with zero inventory, trade through several assets, return

> to zero inventory, and nevertheless extract guaranteed profit solely because

> of the mathematical structure of the market-impact model?

An economically admissible impact model should rule out such negative-cost

round trips. This repository formalizes conditions under which that form of

price manipulation is impossible, and also proves a constructive converse for

the formalized linear model.

## Why this problem matters

Trading one asset can affect not only its own price but also the prices of

related assets. This phenomenon is known as cross-impact.

Cross-impact models appear in:

- multi-asset optimal execution

- transaction-cost modeling

- portfolio liquidation

- market simulation

- execution-algorithm design

- calibration of transient impact kernels

- theoretical studies of market stability and admissibility.

A model can fit observed data and still be structurally defective. In

particular, an impact kernel or cross-asset coupling matrix may accidentally

permit a trader to generate profit through a closed trading cycle.

No-price-manipulation is therefore not merely a desirable empirical feature.

It is a mathematical consistency condition on the model itself.

## What is proved

The formalization establishes a chain of results connecting an exact linear

criterion to a concrete continuous power-law impact model.

At a high level, the proof proceeds as follows:

1. Express the cost of a linear round trip through a compressed quadratic

   positivity condition.

2. Prove an exact necessary-and-sufficient no-price-manipulation criterion for

   the formalized linear model.

3. Show that a positive exponential operator mode produces nonnegative work.

4. Extend the result to finite positive mixtures of exponential modes.

5. Represent a power-law kernel as a positive continuous mixture of

   exponentials through an exact Gamma/Laplace identity.

6. Transfer the finite-mode positivity result to the concrete continuous

   power-law impact model.

7. Add the unaffected-price contribution and prove that its expected value

   vanishes for deterministic finite-step strategies under martingale

   increments.

8. Extend that bridge to random finite-step predictable strategies under

   explicit measurability and integrability assumptions.

9. Prove a converse for the linear model: if the compressed positivity

   criterion fails, then a negative-cost round trip exists.

The result is therefore not only a sufficient construction. For the

formalized linear stage, the development also identifies the failure mode and

constructs a price-manipulation witness.

## Principal final theorem

The principal final declaration is:

    concreteContinuousPowerLaw_predictableNoPriceManipulation

It combines two components:

- the expected unaffected-price cost is zero for a random finite-step

  predictable strategy under conditionally mean-zero price increments; and

- the verified continuous power-law impact contribution is nonnegative.

The conclusion is that expected total execution cost is nonnegative for the

formalized finite-step predictable-strategy interface.

## Exact linear criterion and converse

The linear portion of the development proves both directions.

The forward direction shows that the compressed positivity condition rules

out negative-cost round trips.

The converse shows that when this condition fails, one can construct:

- a negative compressed witness

- a corresponding negative-cost round trip; and

- a formal price-manipulation witness.

This is important because it distinguishes an exact structural criterion from

a merely convenient sufficient condition.

## Why the power-law construction is significant

Power-law decay is commonly used to represent persistent or slowly decaying

market impact.

The formal proof does not assert positivity of the power-law kernel by

inspection. Instead, it derives the result through a structural

representation:

- positive exponential modes are individually admissible

- positive finite mixtures remain admissible

- the power-law kernel is represented as a positive continuous exponential

  mixture;

- the associated impact work inherits nonnegativity under the stated analytic

  assumptions.

This provides a reusable proof pattern for constructing admissible transient

impact kernels from positive mode decompositions.

## Why formal verification adds value

The purpose of the Lean development is not simply to restate a handwritten

proof in another notation.

Lean checks that:

- every hypothesis is explicit

- all dimensions and types match

- positivity assumptions are used where required

- finite-mixture and continuous-mixture arguments compose correctly

- the Gamma/Laplace identity is connected to the impact functional

- the martingale bridge includes the necessary measurability assumptions

- all required products are integrable

- the converse constructs an actual negative-cost witness

- the final theorem depends only on the declared assumptions

- no proof placeholders or custom logical axioms are present.

These checks are especially valuable in mathematical finance, where an

apparently minor omitted assumption can change whether an expected-cost

argument is valid.

## Intended use cases

This repository can be used as:

### A machine-checkable reference

Researchers can inspect the exact assumptions and theorem statements rather

than relying only on an informal summary.

### A model-design guide

The positivity architecture illustrates how admissible cross-impact kernels

can be built from positive operator modes and positive mixtures.

### A validation target

A proposed linear cross-impact model can be compared against the exact

compressed positivity criterion formalized here.

### A foundation for an academic paper

The repository provides an independently buildable formal artifact supporting

the associated mathematical claims.

### A starting point for further formalization

Possible extensions include broader strategy spaces, additional kernel

families, richer stochastic-process interfaces, and a larger formalized

library for market-impact mathematics.

## How a market practitioner can use this result

The repository is not a production execution system, but its theorems provide

a practical model-governance framework for researchers, quantitative

developers, execution teams, and model-risk reviewers.

A practitioner evaluating a proposed cross-impact model can use the result in

the following sequence.

### 1. Identify the round-trip cost operator

Write the model's transient impact contribution as an operator acting on the

trading-rate path. Restrict attention to round trips, meaning strategies whose

net inventory change is zero.

For the formalized linear model, the relevant question is whether the

symmetric part of the compressed cost operator is positive semidefinite on

that zero-net-flow subspace.

### 2. Test the exact linear criterion

The declaration

    no_negative_roundTrip_iff_compressed_positive

states the exact criterion for the formalized linear stage.

This gives a model reviewer two possible outcomes:

- if the compressed operator is positive, negative-cost round trips are ruled

  out in the formalized model;

- if it is not positive, the converse construction shows that a negative-cost

  round trip exists.

Thus the criterion can be used as a structural rejection test before a model

is accepted for calibration or deployment.

### 3. Construct admissible kernels from positive modes

When a transient kernel admits a representation as a positive mixture of

exponential modes, the proof gives a constructive route to nonnegative impact

work.

For a finite approximation, a practitioner can check that:

- every decay rate is positive;

- every operator-valued mode coefficient is positive semidefinite;

- the mixture weights are nonnegative;

- the resulting integrals satisfy the required finiteness assumptions.

This is often easier and safer than attempting to prove positivity directly

from a complicated time-domain kernel.

### 4. Validate power-law implementations through their mixture representation

The verified power-law result uses an exact Gamma/Laplace representation as a

positive continuous mixture of exponentials.

A numerical implementation can therefore be designed or audited through a

positive exponential approximation. Positivity of the mode weights and

operator coefficients should be preserved during discretization and

calibration.

A fitted approximation that introduces negative mixture weights or indefinite

operator modes may lose the no-price-manipulation guarantee even when its

time-domain fit appears accurate.

### 5. Separate impact cost from unaffected-price risk

The final predictable-strategy theorem separates two issues:

- the impact component, which is shown to be nonnegative under the structural

  kernel assumptions; and

- the unaffected-price component, whose expectation vanishes under the stated

  predictability, conditional mean-zero, and integrability assumptions.

This helps distinguish a genuine defect in the impact model from ordinary

profit or loss caused by exposure to unpredictable market-price movements.

### 6. Use the theorem as part of model governance

The formal result can support a model-review checklist:

- Is the trading strategy class the same as, or narrower than, the formalized

  finite-step predictable class?

- Is the strategy coefficient selected using only currently available

  information?

- Are the required price increments and coefficient-times-increment products

  integrable?

- Is the compressed linear round-trip operator positive?

- Are exponential-mode coefficients positive semidefinite?

- Are mixture weights nonnegative?

- Does numerical approximation preserve these properties?

- Are any nonlinear terms outside the scope of the exact converse clearly

  identified?

Passing these checks does not establish empirical accuracy or execution

quality. It establishes that the specified structural mechanism does not

create the particular negative-cost round trips ruled out by the theorem.

## What this repository is not

This is not:

- a trading strategy

- an execution engine

- a calibration package

- evidence that a particular empirical model fits real markets

- a guarantee that a deployed trading system cannot lose money

- a proof that every power-law cross-impact specification is admissible.

The results apply to the mathematical objects and assumptions explicitly

represented in the Lean development.

## Main verified declarations

| File | Declaration | Role |

|---|---|---|

| `ExactLinearStage.lean` | `exact_roundTrip_criterion` | Exact round-trip cost criterion |

| `ExactLinearStage.lean` | `exact_linear_noPriceManipulation_iff` | Exact linear no-price-manipulation equivalence |

| `ConcreteFiniteExponentialMixture.lean` | `concretePositiveOperatorModeWork_nonnegative` | Nonnegative work for one positive exponential mode |

| `ConcreteFiniteExponentialMixture.lean` | `concreteFiniteExponentialMixtureWork_nonnegative` | Closure under finite positive mixtures |

| `PowerLawGammaClosure.lean` | `powerLawExponentialMixture_eq` | Gamma/Laplace power-law representation |

| `ContinuousConcretePowerLawWork.lean` | `concreteContinuousPowerLawWork_integrable_nonnegative` | Integrable nonnegative continuous power-law work |

| `ContinuousConcretePowerLawWork.lean` | `concreteContinuousPowerLaw_financialNoPriceManipulation` | Financial no-price-manipulation result |

| `DeterministicMartingaleBridge.lean` | `deterministicUnaffectedPriceCost_eq_zero` | Zero expected deterministic unaffected-price cost |

| `DeterministicMartingaleBridge.lean` | `concreteContinuousPowerLaw_martingaleNoPriceManipulation` | Deterministic finite-step martingale bridge |

| `ConverseNegativeRoundTrip.lean` | `exists_negative_compressed_witness` | Negative witness when positivity fails |

| `ConverseNegativeRoundTrip.lean` | `exists_negativeCost_roundTrip_of_compressed_failure` | Negative-cost round trip from criterion failure |

| `ConverseNegativeRoundTrip.lean` | `exists_priceManipulation_of_linearCriterion_failure` | Price-manipulation witness |

| `ConverseNegativeRoundTrip.lean` | `no_negative_roundTrip_iff_compressed_positive` | Exact compressed positivity equivalence |

| `PredictableMartingaleBridge.lean` | `predictableUnaffectedPriceCost_eq_zero` | Zero expected predictable unaffected-price cost |

| `PredictableMartingaleBridge.lean` | `concreteContinuousPowerLaw_predictableNoPriceManipulation` | Final predictable-strategy theorem |

A more detailed declaration map is available at:

    docs/theorem_map.md

## Scope and assumptions

The sufficient predictable-strategy result covers finite collections of

trading steps with:

- random strategy coefficients measurable relative to the information

  available when each coefficient is selected;

- integrable price increments

- conditionally mean-zero price increments

- explicitly integrable coefficient-times-increment products

- the stated positivity assumptions on the impact operators

- the stated finite-dimensional and analytic assumptions

- the integrability hypotheses required for the continuous power-law mixture.

The exact converse applies to the formalized linear model.

## Explicit limitations

This repository does not prove:

- a general continuous-time stochastic-integral theorem

- a general semimartingale result

- an Itô-integration theorem

- a nonlinear power-law converse

- empirical correctness of any particular cross-impact calibration

- automatic discharge of every analytic or integrability assumption.

The finite-step predictable interface captures a meaningful stochastic trading

class without claiming a more general continuous-time result than has actually

been formalized.

## Verification status

The publication repository was independently rebuilt from its pinned Lean and

Mathlib dependencies.

Verified state:

- complete Lake build: passed

- build jobs: 8,597

- direct compilation of the final bridge: passed

- compiler and linter warnings: 0

- audited Lean source files: 17

- expected public declarations reconciled: 17 of 17

- `sorry`: 0

- `admit`: 0

- custom axioms: 0

- `opaque` declarations: 0

- custom constants: 0.

The full proof-log-to-Lean reconciliation report is available at:

    docs/proof_log_to_lean_reconciliation.md

## Reproducibility

The repository pins:

- Lean `v4.32.0-rc1`

- the corresponding Mathlib revision through `lake-manifest.json`

- all project source files required for a clean build.

Install Lean through `elan`, then run:

    lake exe cache get

    lake build

To compile the final predictable bridge directly after the library build:

    lake env lean CrossImpactNoPriceManipulation/PredictableMartingaleBridge.lean

## Repository structure

- `CrossImpactNoPriceManipulation/` — Lean source modules.

- `CrossImpactNoPriceManipulation.lean` — root import file.

- `docs/theorem_map.md` — theorem and declaration map.

- `docs/proof_log_to_lean_reconciliation.md` — final verification audit.

- `CITATION.cff` — citation metadata.

- `RELEASE_NOTES.md` — release summary.

- `lakefile.toml` — Lake project configuration.

- `lake-manifest.json` — pinned dependency manifest.

- `lean-toolchain` — pinned Lean toolchain.

## Citation and archival record

Archived release DOI:

    10.5281/zenodo.21250432

Citation metadata is provided in `CITATION.cff`.

GitHub repository:

    https://github.com/cadottea/lean-cross-impact-no-price-manipulation

## License

Apache License 2.0.

