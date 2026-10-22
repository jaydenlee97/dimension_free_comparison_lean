# Manuscript-to-Lean coverage

This table distinguishes proving a mathematical statement from checking every
line of the manuscript's chosen proof. All completed entries are imported by
`GaussianMixturePaper.lean`; `Audit.lean` checks their transitive dependencies.
The strict objective of reproducing every manuscript proof route remains **incomplete**.
The expanded coverage below includes the previously missing probabilistic model,
identifiability, optimal constants, matrix construction, PDE, and explicit envelopes.

For a compact entry point, see [proof status](../PROOF_STATUS.md) and the
[theorem map](theorem-map.md).

## Main theorem and numbered lemmas

| Claim | Status and exact scope | Principal declarations |
|---|---|---|
| Gaussian mixture definitions | Proved normalization, positivity, actual Gaussian convolution, support-subtype transport, explicit finite divergences | `GaussianComparison.GaussianModel.*`, `GaussianMixturePaper.theorem1_ambient` |
| Theorem 1, (1.1)-(1.2) | Proved for every dimension, M >= 0, arbitrary supported probability priors, both chi-square directions, exact constants | `theorem1`, `theorem1_with_finiteness`, `theorem1_ambient` |
| Lemma 1, (2.5) | Proved finiteness, C1 on all of R, all three derivatives for every t including 0; posterior means are canonical normalized weighted integrals | `GaussianComparison.GaussianModel.lemma1` |
| Lemma 2, (A.3) | Proved for an actual C1 test function with canonical gradient and the stated exponential growth bound; both sides absolutely integrable | `lemma2_gaussian_integration_by_parts` |
| Lemma 3, (A.11)-(A.14) | Proved both exact numerical integral bounds and polynomial domination; works for all real c | `lemma3_exponential`, `lemma3_polynomial`, `one_add_radius_pow_le` |
| Lemma 4, (A.15)-(A.17) | Proved from joint measurability, AE C1 slices and nonnegative sum-integrable compact-interval envelopes; derivative measurability is derived, not assumed | `lemma4` |
| Lemma 5(i), (A.19) | Proved exact lower/upper density envelopes | `density_envelopes` |
| Lemma 5(ii), (A.20)-(A.21) | Proved exact derivative integral and relative derivative bound | `density_hasDerivAt_time`, `density_deriv_time_bound` |
| Lemma 5(iii), (A.22) | Proved spatial gradient as the exact vector integral | `density_gradient_space` |
| Lemma 5(iv) | Proved joint C1, with a stronger C-infinity result | `density_contDiff_one`, `density_contDiff_joint` |
| Lemma 6, (A.41)-(A.43) | Proved every real likelihood-ratio power, canonical gradients, exact uniform growth constants, log-ratio bound | `lemma6_gradient`, `lemma6`, `logRatio_bound` |
| Main KL and chi-square proof | Deterministic mean-scaling derivative comparisons and endpoint bounds proved; no stochastic realization is assumed | `GaussianComparison.MeanScalingKL`, `MeanScalingIdentities`, `MeanScalingChiComparison` |
| Remark 1 Gaussian pair | Exact Jeffreys/chi-square/Hellinger formulas proved, with positive denominator for M > 0 | `remark1_gaussian_formulas`, `remark1_hellinger_denominator_pos` |
| Section 3 concrete identities | Proved for actual KL/Hellinger/chi-square generators, their second derivatives, the exact Fisher weights and actual likelihood-score gradient, for every real t | `GaussianComparison.GaussianModel.deBruijn_three_generators` |


## Additional mathematical statements

| Claim | Status and exact scope | Principal declarations |
|---|---|---|
| Identifiability and ratio denominators | Gaussian convolution is injective from AE equality; H² is zero iff the priors are equal, also for ambient supported measures | `mixtureDensity_injective_ae`, `hellingerSq_mixture_eq_zero_iff`, `hellingerSq_ambient_eq_zero_iff` |
| Remark 1 optimal constants, (1.3)-(1.5) | Exact suprema over every finite dimension and distinct probability priors; both numerical bounds for M > 0 | `optimalKL_bounds`, `optimalChiSq_bounds`, `optimal_constant_denominator_pos` |
| Remark 1 asymptotics | Both O(1) claims, leading limits 2 and 4, lower chi bound asymptotic to exp(4M²)/2, and upper/lower ratio tending to 36; uniform factor-36 bound also proved | `optimalKL_asymptotic`, `optimalChiSq_log_asymptotic`, `optimalKL_leading_coefficient`, `optimalChiSq_leading_exponent`, `chiSq_bounds_ratio_tendsto36` |
| Independent Gaussian observation model, (2.1) | Actual probability product measure, independence, joint density, and distributional equality for tΘ+Z | `independent_observation_joint_density`, `independent_observation_law`, `priorVector_independent_noise` |
| Conditional-expectation posterior, (2.3) | Explicit normalized posterior Markov kernel, Bayes disintegration, first moment, and actual conditional expectation given σ(tΘ+Z) | `posteriorJoint_eq_density`, `posteriorKernel_mean`, `posterior_is_conditionalExpectation_independent` |
| Global Hellinger monotonicity and range | D is nondecreasing on [0,infinity), and 0 <= D(t) <= 2 at every real time | `hellinger_interpolation_monotone`, `hellinger_interpolation_range` |
| Generic f-divergence and matrix definition, (3.1) | Actual generator integrals agree with the paper's three divergences; every matrix entry integrable; exact matrix trace equals scalar integral | `GaussianComparison.GaussianModel.densityFDivergence_kl`, `densityFDivergence_hellinger`, `densityFDivergence_chiSq`, `generatorFisherMatrix_trace` |
| Density PDE, (3.2) | Exact divergence and Laplacian of the actual density, with coordinate derivative definitions; all real times, including zero | `density_PDE` |
| Section 3 spatial boundary values | Radial generator-density vector and full gradient of q f(p/q) tend to zero at spatial infinity, with all growth premises discharged for the three generators | `paperGenerator_boundary_conditions` |
| Literal A.3.6 envelopes | Exact six P/Q functions, actual integrand and derivative domination, integrability, Gaussian component bounds, and page 20-21 numerical integral bounds | `appendix_raw_domination`, `appendix_envelopes_integrable`, `gaussian_component_deriv_bound`, `integral_PC_add_QC_bound`, `integral_PA_add_QA_bound` |
| Normalization differentiation, (A.44) | Actual time derivative is integrable and integrates to zero | `integral_density_deriv_zero` |
| Explicit chi finiteness bound after (A.51) | 0 <= C(t) <= exp(T²M²/2) S(3TM;d) - 1 for abs(t) <= T | `chiSq_explicit_finiteness_bound` |


## Explicit analytic proof routes

| Claim | Status and exact scope | Principal declarations |
|---|---|---|
| Literal cubic cutoff, (A.34)-(A.38) | Exact piecewise polynomial; C1, compact support, range, 3/(2R) gradient bound; dominated convergence; integrated boundary error tends to zero with the exact Gaussian constant; full Fubini assembly proves Lemma 2 by this route | `PaperCutoff.gradient_chi_bound`, `PaperCutoff.gaussian_boundaryTerm_bound`, `PaperCutoff.gaussian_integration_by_parts_via_cutoff`, `PaperCutoff.lemma2_via_cutoff` |
| General generator identity, (3.3) | Derived from chain rules, dominated differentiation and Gaussian IBP for positive-argument C2 generators with local exponential growth; actual matrix trace, all real times | `GaussianComparison.GaussianModel.generalFDivergence_hasDerivAt`, `general_deBruijn_matrix` |
| Concrete generator hypotheses | Convexity on [0,infinity), C2 on (0,infinity), and all local growth hypotheses are proved for all three generators; the generic identity is instantiated | `GaussianComparison.GaussianModel.paperGenerator_convex`, `paperGenerator_admissible`, `paperGenerator_general_deBruijn` |
| Section 3 first and second time derivatives | Actual first and second time derivatives of q f(p/q) are integrable; their sum has one integrable Gaussian envelope uniformly on each bounded time interval | `GaussianComparison.GaussianModel.paperGeneratorDensity_time_derivatives_integrable`, `paperGeneratorDensity_time_derivatives_local_envelope` |

Groups beginning with `GaussianComparison.GaussianModel` use that namespace
for their remaining names. Other names belong to `GaussianMixturePaper`,
including its `PaperCutoff` subnamespace.

## Remaining proof-route distinctions

The broad external Proposition 6 cited in Section 3 has not been ported as a
standalone theorem for arbitrary PDE families and linear operators. The project
proves the applicable general-generator Gaussian identity directly and instantiates
it for all three generators with every growth premise discharged. The spatial boundary theorems
currently state decay at infinity, not an independently formalized surface-flux
integral over expanding spheres. These distinctions matter for the user's strict
request to check every argument in the manuscript's chosen proof route.

The probability measures are constructed with their actual densities, and the
posterior is an actual conditional expectation. Divergences retain the paper's
explicit density-integral definitions, with finiteness proofs. Identification
with Mathlib's separately named measure-level information divergences would be
an interoperability addition; it is not assumed by any mathematical result here.

No admitted propositions or analytic axioms stand in for remaining work.
`verification/latest/status.json` retains `whole_paper_complete: false`.

## Interpretation of proof evidence

The successful local build checks the complete project source closure against
the pinned dependency artifacts. The audit traverses every loaded project
declaration, including generated private declarations, and rejects every
axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Required public
endpoints cannot silently disappear from the default build. The verifier also
rejects any project source module that is absent from the public import closure.
Source hashes bind the evidence to these exact Lean files. This does not replace human
checking of whether formal definitions and theorem types represent the paper;
that semantic check is documented above and in `docs/mathematical-audit.md`.
