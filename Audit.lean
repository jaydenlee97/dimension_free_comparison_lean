import GaussianMixturePaper
import Lean

/-!
Inspect the transitive axiom closure of every loaded project declaration,
including private generated declarations. This command fails on an
unapproved axiom, and cannot succeed with an empty project import.
-/
open Lean Elab Command

elab "#audit_project" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut theoremCount : Nat := 0
  for (name, ci) in env.constants.toList do
    let s := name.toString
    if s.startsWith "GaussianComparison." ||
       s.startsWith "GaussianMixturePaper." ||
       s.startsWith "_private.GaussianComparison." ||
       s.startsWith "_private.GaussianMixturePaper." then
      let axioms ← collectAxioms name
      for a in axioms do
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          throwError "Unapproved axiom {a} in {name}"
      count := count + 1
      if ci.isTheorem then
        theoremCount := theoremCount + 1
        let axs := String.intercalate "," ((axioms.qsort Name.lt).toList.map toString)
        logInfo m!"AUDIT|{name}|{axs}"
  unless theoremCount > 100 do
    throwError "Incomplete project import: only {theoremCount} theorem declarations"
  logInfo m!"AUDIT_TOTAL|{count}|{theoremCount}"

#audit_project




#check GaussianMixturePaper.theorem1
#check GaussianMixturePaper.theorem1_with_finiteness
#check GaussianMixturePaper.theorem1_ambient
#check GaussianComparison.GaussianModel.lemma1
#check GaussianMixturePaper.lemma2_gaussian_integration_by_parts
#check GaussianMixturePaper.lemma3_exponential
#check GaussianMixturePaper.lemma3_polynomial
#check GaussianMixturePaper.lemma4
#check GaussianMixturePaper.density_envelopes
#check GaussianMixturePaper.density_hasDerivAt_time
#check GaussianMixturePaper.density_deriv_time_bound
#check GaussianMixturePaper.density_gradient_space
#check GaussianMixturePaper.density_contDiff_one
#check GaussianMixturePaper.lemma6
#check GaussianMixturePaper.lemma6_gradient
#check GaussianMixturePaper.remark1_gaussian_formulas
#check GaussianMixturePaper.remark1_hellinger_denominator_pos
#check GaussianComparison.GaussianModel.deBruijn_three_generators
#check GaussianMixturePaper.mixtureDensity_injective_ae
#check GaussianMixturePaper.hellingerSq_mixture_eq_zero_iff
#check GaussianMixturePaper.hellingerSq_ambient_eq_zero_iff
#check GaussianMixturePaper.optimal_constant_denominator_pos
#check GaussianMixturePaper.optimalKL_bounds
#check GaussianMixturePaper.optimalChiSq_bounds
#check GaussianMixturePaper.optimalKL_asymptotic
#check GaussianMixturePaper.optimalChiSq_log_asymptotic
#check GaussianMixturePaper.optimalKL_leading_coefficient
#check GaussianMixturePaper.optimalChiSq_leading_exponent
#check GaussianMixturePaper.chiSq_comparison_factor36
#check GaussianMixturePaper.chiSq_bounds_ratio_tendsto36
#check GaussianMixturePaper.posteriorJoint_eq_density
#check GaussianMixturePaper.posteriorKernel_mean
#check GaussianMixturePaper.posterior_is_conditionalExpectation
#check GaussianMixturePaper.independent_observation_joint_density
#check GaussianMixturePaper.independent_observation_law
#check GaussianMixturePaper.priorVector_independent_noise
#check GaussianMixturePaper.posterior_is_conditionalExpectation_independent
#check GaussianMixturePaper.density_PDE
#check GaussianMixturePaper.paperGenerator_boundary_conditions
#check GaussianMixturePaper.hellinger_interpolation_range
#check GaussianMixturePaper.hellinger_interpolation_monotone
#check GaussianMixturePaper.appendix_envelopes_integrable
#check GaussianMixturePaper.appendix_raw_domination
#check GaussianMixturePaper.integral_density_deriv_zero
#check GaussianMixturePaper.gaussian_component_bound
#check GaussianMixturePaper.gaussian_component_deriv_bound
#check GaussianMixturePaper.integral_PC_add_QC_bound
#check GaussianMixturePaper.integral_PA_add_QA_bound
#check GaussianMixturePaper.chiSq_explicit_finiteness_bound
#check GaussianComparison.GaussianModel.densityFDivergence_kl
#check GaussianComparison.GaussianModel.densityFDivergence_hellinger
#check GaussianComparison.GaussianModel.densityFDivergence_chiSq
#check GaussianComparison.GaussianModel.integrable_generatorFisherMatrix_entry
#check GaussianComparison.GaussianModel.generatorFisherMatrix_trace
#check GaussianComparison.GaussianModel.deBruijn_matrix
#check GaussianMixturePaper.PaperCutoff.contDiff_chi
#check GaussianMixturePaper.PaperCutoff.chi_hasCompactSupport
#check GaussianMixturePaper.PaperCutoff.gradient_chi_bound
#check GaussianMixturePaper.PaperCutoff.tendsto_integral_mul_chi
#check GaussianMixturePaper.PaperCutoff.tendsto_boundaryTerm
#check GaussianMixturePaper.PaperCutoff.gaussian_boundaryTerm_bound
#check GaussianMixturePaper.PaperCutoff.gaussian_integration_by_parts_via_cutoff
#check GaussianMixturePaper.PaperCutoff.lemma2_via_cutoff
#check GaussianComparison.GaussianModel.generalFDivergence_hasDerivAt
#check GaussianComparison.GaussianModel.general_deBruijn_matrix
#check GaussianComparison.GaussianModel.paperGenerator_convex
#check GaussianComparison.GaussianModel.paperGenerator_admissible
#check GaussianComparison.GaussianModel.paperGenerator_general_deBruijn
#check GaussianComparison.GaussianModel.paperGeneratorDensity_time_derivatives_integrable
#check GaussianComparison.GaussianModel.paperGeneratorDensity_time_derivatives_local_envelope
#check GaussianComparison.GaussianModel.integrable_generalFDivergence
#check GaussianComparison.GaussianModel.generalFDivergence_contDiff_one
#check GaussianComparison.GaussianModel.paperGeneratorDensity_contDiff_two
