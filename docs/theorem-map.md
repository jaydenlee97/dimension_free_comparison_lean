# Theorem map

Start with [PROOF_STATUS.md](../PROOF_STATUS.md) for the checked scope and
[coverage.md](coverage.md) for hypotheses and proof-route qualifications.
[GaussianMixturePaper.lean](../GaussianMixturePaper.lean) imports the complete
public development. [Audit.lean](../Audit.lean) displays and audits its
paper-facing endpoints.

In the table, **P** denotes namespace `GaussianMixturePaper` and **G** denotes
`GaussianComparison.GaussianModel`. Append the displayed declaration name
to that namespace. Each source link opens the file containing the declaration.

| Paper location | Principal declaration(s) | Source |
|---|---|---|
| Theorem 1, (1.1)–(1.2), supported ambient priors | P.`theorem1_ambient` | [AmbientPrior.lean](../GaussianMixturePaper/AmbientPrior.lean) |
| Theorem 1, ball-subtype formulation and finiteness | P.`theorem1`, P.`theorem1_with_finiteness` | [Theorem1.lean](../GaussianMixturePaper/Theorem1.lean) |
| Lemma 1, (2.5), all real times and C¹ | G.`lemma1` | [GlobalRegularity.lean](../GaussianMixturePaper/GlobalRegularity.lean) |
| Lemma 2, (A.3) | P.`lemma2_gaussian_integration_by_parts` | [AnalyticLemmas.lean](../GaussianMixturePaper/AnalyticLemmas.lean) |
| Lemma 3, (A.11)–(A.14), exact constants | P.`lemma3_exponential`, P.`lemma3_polynomial` | [GaussianEnvelope.lean](../GaussianMixturePaper/GaussianEnvelope.lean) |
| Lemma 4, (A.15)–(A.17) | P.`lemma4` | [DominatedDifferentiation.lean](../GaussianMixturePaper/DominatedDifferentiation.lean) |
| Lemma 5, all four parts | P.`density_envelopes`, P.`density_hasDerivAt_time`, P.`density_deriv_time_bound`, P.`density_gradient_space`, P.`density_contDiff_one` | [DensityRegularity.lean](../GaussianMixturePaper/DensityRegularity.lean) |
| Lemma 6, (A.41)–(A.43) | P.`lemma6`, P.`lemma6_gradient` | [AnalyticLemmas.lean](../GaussianMixturePaper/AnalyticLemmas.lean) |
| Remark 1, Gaussian example | P.`remark1_gaussian_formulas` | [Sharpness.lean](../GaussianMixturePaper/Sharpness.lean) |
| Remark 1, distinct-prior ratio denominators | P.`hellingerSq_ambient_eq_zero_iff` | [Identifiability.lean](../GaussianMixturePaper/Identifiability.lean) |
| Remark 1, (1.3)–(1.5) and asymptotics | P.`optimalKL_bounds`, P.`optimalChiSq_bounds`, P.`optimalKL_asymptotic`, P.`optimalChiSq_log_asymptotic` | [OptimalConstants.lean](../GaussianMixturePaper/OptimalConstants.lean) |
| Observation law, (2.1) | P.`independent_observation_law` | [ObservationLaw.lean](../GaussianMixturePaper/ObservationLaw.lean) |
| Posterior conditional expectation, (2.3) | P.`posterior_is_conditionalExpectation_independent` | [PosteriorObservation.lean](../GaussianMixturePaper/PosteriorObservation.lean) |
| Hellinger interpolation monotonicity | P.`hellinger_interpolation_monotone` | [InterpolationConsequences.lean](../GaussianMixturePaper/InterpolationConsequences.lean) |
| Fisher matrix and trace, (3.1) | G.`generatorFisherMatrix_trace`, G.`deBruijn_matrix` | [FisherMatrix.lean](../GaussianMixturePaper/FisherMatrix.lean) |
| Density PDE, (3.2), and spatial boundary decay | P.`density_PDE`, P.`paperGenerator_boundary_conditions` | [DensityPDE.lean](../GaussianMixturePaper/DensityPDE.lean) |
| General-generator identity, (3.3), with explicit growth assumptions | G.`general_deBruijn_matrix` | [GeneralDeBruijn.lean](../GaussianMixturePaper/GeneralDeBruijn.lean) |
| All three concrete generator instances | G.`paperGenerator_admissible`, G.`paperGenerator_general_deBruijn` | [GeneralGeneratorInstances.lean](../GaussianMixturePaper/GeneralGeneratorInstances.lean) |
| Section 3, first/second time-derivative domination | G.`paperGeneratorDensity_time_derivatives_local_envelope` | [SecondTimeRegularity.lean](../GaussianMixturePaper/SecondTimeRegularity.lean) |
| Literal cutoff proof, (A.34)–(A.38), through (A.3) | P.`PaperCutoff.lemma2_via_cutoff` | [Cutoff.lean](../GaussianMixturePaper/Cutoff.lean) |
| A.3.6, exact P/Q envelopes and normalization derivative | P.`appendix_raw_domination`, P.`appendix_envelopes_integrable`, P.`integral_density_deriv_zero` | [AppendixDomination.lean](../GaussianMixturePaper/AppendixDomination.lean) |

The [required-theorem manifest](../verification/required-theorems.json) lists
all 73 mandatory audited endpoints. The retained
[statement log](../verification/latest/axioms-and-statements.log) displays
their full Lean types; [axiom dependencies](../verification/latest/theorem-axioms.json)
are recorded separately. Read the types when checking quantifier order,
normalization, or assumptions; names alone do not establish correspondence.
