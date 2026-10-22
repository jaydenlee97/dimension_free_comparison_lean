# Gaussian Mixture Lean Verification

This project targets Jeonghwan Lee and Cong Ma, *Dimension-free comparison
inequalities between f-divergences for Gaussian location mixtures*, manuscript
dated October 22, 2026 (21 pages). The manuscript is identified by its
[metadata and SHA256](verification/manuscript.json); the PDF is not distributed
in this repository.

The public entry point is [GaussianMixturePaper.lean](GaussianMixturePaper.lean).
See [proof status](PROOF_STATUS.md), the [theorem map](docs/theorem-map.md),
and the [detailed coverage table](docs/coverage.md).

Theorem 1 and all six numbered lemmas have proved mathematical counterparts.
This revision also proves Remark 1's optimal-constant suprema and asymptotics,
Gaussian-mixture identifiability, the independent observation model and actual
conditional-expectation posterior, the Fisher matrix and density PDE, the literal
cubic cutoff, and the explicit appendix domination bounds. **This is not yet a claim
that every argument in the manuscript has been formalized.** Exact remaining
obligations and differences in proof route are listed in the [coverage table](docs/coverage.md).

## Main results

`GaussianMixturePaper.theorem1_ambient` treats arbitrary Borel probability
measures on Euclidean space concentrated on the closed radius-M ball, in any
natural dimension and for M >= 0. It proves finiteness as well as

$$
\mathrm{KL}(P_\mu\|P_\nu)+\mathrm{KL}(P_\nu\|P_\mu)
\le (2M^2+4) H^2(P_\mu,P_\nu),
$$

$$
\max\{\chi^2(P_\mu\|P_\nu),\chi^2(P_\nu\|P_\mu)\}
\le (18e^{4M^2}-2)H^2(P_\mu,P_\nu).
$$

The densities are actual Gaussian convolution integrals. Squared Hellinger
distance is the integral of the squared difference of square roots, without
a factor 1/2. There are no derivative identities, comparison inequalities,
or analytic certificate structures among the main theorem's assumptions.

## Reproduce

Install the toolchain named in `lean-toolchain`, then run in this directory:

```bash
lake exe cache get
bash verify.sh --fresh
```

The first command obtains dependency artifacts for the pinned Mathlib commit.
The second deletes only this project's generated build outputs, rebuilds the
entire public root, and audits the transitive axiom dependencies of every
loaded project declaration, including private generated declarations. It
requires the named manuscript endpoints in `verification/required-theorems.json`
to appear in the audit. Every project source module must belong to the public
root's import closure. A missing module, missing endpoint, or unapproved axiom
fails the run.
Do not run `lake update` when reproducing this pinned version.

The allowed foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Source scanning additionally rejects `sorry`, `admit`, new axioms,
`native_decide`, `unsafe`, and `implemented_by`. Compilation and dependency
inspection are the substantive checks; a source scan alone is insufficient.

The fresh local build and audit passed: 1,105 project declarations were checked,
including 953 theorem declarations and all 73 required endpoints.
All 42 project modules belong to the verified public import closure.

`verification/latest/` contains build logs, displayed theorem types, the
declaration audit, source SHA256 values, and machine-readable status. The
theorem count includes generated auxiliary declarations and is not a count
of manuscript theorems. CI configuration is included, but this deliverable's
[CI workflow](.github/workflows/lean.yml) has not yet been run on GitHub.

## Where to read

| Paper result | Formal module |
|---|---|
| Theorem 1 | [GaussianMixturePaper/Theorem1.lean](GaussianMixturePaper/Theorem1.lean) |
| Ambient supported priors | [GaussianMixturePaper/AmbientPrior.lean](GaussianMixturePaper/AmbientPrior.lean) |
| Lemma 1, all real times and C1 | [GaussianMixturePaper/GlobalRegularity.lean](GaussianMixturePaper/GlobalRegularity.lean) |
| Lemmas 2 and 6 | [GaussianMixturePaper/AnalyticLemmas.lean](GaussianMixturePaper/AnalyticLemmas.lean) |
| Lemma 3, exact constants | [GaussianMixturePaper/GaussianEnvelope.lean](GaussianMixturePaper/GaussianEnvelope.lean) |
| Lemma 4, including derivative measurability | [GaussianMixturePaper/DominatedDifferentiation.lean](GaussianMixturePaper/DominatedDifferentiation.lean) |
| Lemma 5, all four parts | [GaussianMixturePaper/DensityRegularity.lean](GaussianMixturePaper/DensityRegularity.lean) |
| Three concrete de Bruijn identities | [GaussianMixturePaper/DeBruijn.lean](GaussianMixturePaper/DeBruijn.lean) |
| Remark 1 Gaussian calculations | [GaussianMixturePaper/Sharpness.lean](GaussianMixturePaper/Sharpness.lean) |
| Identifiability and positive ratio denominators | [GaussianMixturePaper/Identifiability.lean](GaussianMixturePaper/Identifiability.lean) |
| Optimal constants and asymptotics | [GaussianMixturePaper/OptimalConstants.lean](GaussianMixturePaper/OptimalConstants.lean) |
| Independent observation and posterior conditional expectation | [GaussianMixturePaper/ObservationLaw.lean](GaussianMixturePaper/ObservationLaw.lean), [PosteriorModel.lean](GaussianMixturePaper/PosteriorModel.lean), [PosteriorObservation.lean](GaussianMixturePaper/PosteriorObservation.lean) |
| Hellinger monotonicity on the full half-line | [GaussianMixturePaper/InterpolationConsequences.lean](GaussianMixturePaper/InterpolationConsequences.lean) |
| Actual generalized Fisher matrix | [GaussianMixturePaper/FisherMatrix.lean](GaussianMixturePaper/FisherMatrix.lean) |
| Density PDE and boundary decay | [GaussianMixturePaper/DensityPDE.lean](GaussianMixturePaper/DensityPDE.lean) |
| Literal cubic cutoff and boundary integrals | [GaussianMixturePaper/Cutoff.lean](GaussianMixturePaper/Cutoff.lean) |
| Exact appendix P/Q envelopes | [GaussianMixturePaper/AppendixDomination.lean](GaussianMixturePaper/AppendixDomination.lean) |
| General generator identity and concrete hypotheses | [GaussianMixturePaper/GeneralDeBruijn.lean](GaussianMixturePaper/GeneralDeBruijn.lean), [GeneralGeneratorInstances.lean](GaussianMixturePaper/GeneralGeneratorInstances.lean) |
| First/second time-derivative domination | [GaussianMixturePaper/SecondTimeRegularity.lean](GaussianMixturePaper/SecondTimeRegularity.lean) |

## Repository structure

| Path | Purpose |
|---|---|
| [GaussianMixturePaper.lean](GaussianMixturePaper.lean) | Public root importing all project modules |
| [GaussianMixturePaper/](GaussianMixturePaper/) | Manuscript statements and analytic proofs |
| [GaussianComparison/](GaussianComparison/) | Verified upstream comparison development |
| [PROOF_STATUS.md](PROOF_STATUS.md) and [docs/](docs/) | Checked scope, theorem map and mathematical qualifications |
| [Audit.lean](Audit.lean), [verify.sh](verify.sh), [scripts/](scripts/) | Complete import-closure and axiom audit |
| [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), [lake-manifest.json](lake-manifest.json) | Pinned, reproducible dependencies |
| [verification/](verification/) | Required endpoints, provenance and retained local evidence |
| [.github/workflows/lean.yml](.github/workflows/lean.yml) | Build and audit on pushes and pull requests |

The presentation follows the public entry-point and verification structure of
[passk-lean](https://github.com/chandramaulichak108/passk-lean) and
[bcsi-lean-verification](https://github.com/congma1028/bcsi-lean-verification).
See [reference notes](docs/reference-repositories.md) for the comparison.

## Provenance and environment

The 19 files under `GaussianComparison/` are unchanged from
`congma1028/GMM-distance`, commit
`dfe71f581e12929d848995f27b9865eccd5fa4c8`, subdirectory
`dimension_free_comparison_gaussian_mixtures_lean_formalization/GaussianComparison`.
Their Git blob hashes were checked against GitHub during this work; see
`verification/upstream-provenance.json`. The new manuscript-facing modules,
audit, reproducible package configuration, and coverage documentation extend
that development. Original notices are retained; no replacement license is
asserted for upstream material.

Pinned Lean: `v4.33.0-rc1`. Pinned Mathlib:
`79d0395a1825a6264ad5d269e35e60537518955e`. All transitive dependency revisions
are recorded in `lake-manifest.json`. The source manuscript's metadata and SHA256
are recorded in `verification/manuscript.json`.

The local host required a narrow executable-path compatibility shim; it does
not modify Lean or its proof checker. `docs/runtime.md` records this detail.
Ordinary installations should use the reproduction commands above directly.

## Manuscript qualifications

The ratios in Remark 1 require M > 0. At M = 0, its distinct-prior class is
empty and its displayed lower-bound ratios contain 0/0. Theorem 1 itself is
verified also at M = 0.

Section 3 should place the KL and Hellinger generators in C2((0,infinity)),
with continuous extensions at zero. They are not differentiable at zero.
All mixture density ratios in the proof are strictly positive. The concrete
de Bruijn identities here hold at t = 0 directly, without cancellation of t.
