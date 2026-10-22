import GaussianComparison.MeanScalingIntegration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Group.Integral

/-!
# Observation model and posterior conditioning

The conditional distribution is constructed from the normalized Gaussian
likelihood. Its first moment is the posterior used in the analytic proof.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open GaussianComparison.GaussianModel

namespace GaussianMixturePaper

variable {d : ℕ} {M : ℝ}

theorem integrable_scaled_likelihood_product (μ : Measure (Ball d M))
    [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (fun p : Space d × Ball d M => phi (p.1 - t • p.2.val))
      (volume.prod μ) := by
  have hc : Continuous (fun p : Space d × Ball d M => phi (p.1 - t • p.2.val)) := by
    unfold phi
    fun_prop
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun θ => integrable_phi_sub (t • θ.val)
  · have heq : (fun θ : Ball d M => ∫ x : Space d, ‖phi (x - t • θ.val)‖) =
        (fun _ : Ball d M => (1 : ℝ)) := by
      funext θ
      simp_rw [Real.norm_eq_abs, abs_of_pos (phi_pos _)]
      exact integral_phi_sub (t • θ.val)
    rw [heq]
    exact integrable_const 1

theorem integral_meanScaledDensity_all (μ : Measure (Ball d M))
    [IsProbabilityMeasure μ] (t : ℝ) :
    (∫ x : Space d, meanScaledDensity μ t x) = 1 := by
  unfold meanScaledDensity
  rw [integral_integral_swap (integrable_scaled_likelihood_product μ t)]
  simp_rw [integral_phi_sub]
  simp

theorem integrable_meanScaledDensity_all (μ : Measure (Ball d M))
    [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (meanScaledDensity μ t) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_meanScaledDensity_all]
  norm_num

/-- The observation law expressed through its actual Lebesgue density. -/
def observationMeasure (μ : Measure (Ball d M)) (t : ℝ) : Measure (Space d) :=
  volume.withDensity (fun x => ENNReal.ofReal (meanScaledDensity μ t x))

theorem observationMeasure_isProbabilityMeasure (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (observationMeasure μ t) := by
  constructor
  rw [observationMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_meanScaledDensity_all μ t)
      (Filter.Eventually.of_forall fun x => (meanScaledDensity_pos hM μ t x).le),
    integral_meanScaledDensity_all]
  simp

/-- The posterior likelihood ratio against the prior. -/
def posteriorWeight (μ : Measure (Ball d M)) (t : ℝ)
    (x : Space d) (θ : Ball d M) : ℝ :=
  phi (x - t • θ.val) / meanScaledDensity μ t x

theorem continuous_posteriorWeight (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    Continuous (Function.uncurry (posteriorWeight μ t)) := by
  apply Continuous.div
  · unfold phi
    fun_prop
  · exact (continuous_meanScaledDensity_space μ t).comp continuous_fst
  · exact fun p => (meanScaledDensity_pos hM μ t p.1).ne'

theorem posteriorWeight_nonneg (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ)
    (x : Space d) (θ : Ball d M) : 0 ≤ posteriorWeight μ t x θ :=
  div_nonneg (phi_pos _).le (meanScaledDensity_pos hM μ t x).le

theorem integrable_posteriorWeight (_hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) (x : Space d) :
    Integrable (posteriorWeight μ t x) μ := by
  have hc : Continuous (fun θ : Ball d M => phi (x - t • θ.val)) := by
    unfold phi
    fun_prop
  have hi : Integrable (fun θ : Ball d M => phi (x - t • θ.val)) μ := by
    simpa using hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  exact hi.div_const _

theorem integral_posteriorWeight (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) (x : Space d) :
    (∫ θ, posteriorWeight μ t x θ ∂μ) = 1 := by
  unfold posteriorWeight
  rw [integral_div]
  exact div_self (meanScaledDensity_pos hM μ t x).ne'

/-- A measurable family of posterior probability measures. -/
def posteriorKernel (_hM : 0 ≤ M) (μ : Measure (Ball d M))
    [IsProbabilityMeasure μ] (t : ℝ) : Kernel (Space d) (Ball d M) :=
  (Kernel.const (Space d) μ).withDensity
    (fun x θ => ENNReal.ofReal (posteriorWeight μ t x θ))

theorem posteriorKernel_apply (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) (x : Space d) :
    posteriorKernel hM μ t x = μ.withDensity
      (fun θ => ENNReal.ofReal (posteriorWeight μ t x θ)) := by
  rw [posteriorKernel, Kernel.withDensity_apply]
  · rfl
  · exact (continuous_posteriorWeight hM μ t).measurable.ennreal_ofReal

instance posteriorKernel_isMarkovKernel (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    IsMarkovKernel (posteriorKernel hM μ t) := by
  constructor
  intro x
  constructor
  rw [posteriorKernel_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_posteriorWeight hM μ t x)
      (Filter.Eventually.of_forall fun θ => posteriorWeight_nonneg hM μ t x θ),
    integral_posteriorWeight hM μ t x]
  simp

/-- The first moment of the actual conditional probability kernel is the
posterior vector in equation (2.3). -/
theorem posteriorKernel_mean (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) (x : Space d) :
    (∫ θ : Ball d M, θ.val ∂posteriorKernel hM μ t x) =
      meanScaledPosterior μ t x := by
  have hw : Measurable (fun θ : Ball d M => ENNReal.ofReal (posteriorWeight μ t x θ)) :=
    ((continuous_posteriorWeight hM μ t).comp
      ((continuous_const : Continuous (fun _ : Ball d M => x)).prodMk continuous_id)).measurable.ennreal_ofReal
  rw [posteriorKernel_apply,
    integral_withDensity_eq_integral_toReal_smul hw
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (posteriorWeight_nonneg hM μ t x _)]
  simp_rw [posteriorWeight, div_eq_mul_inv, mul_comm (phi _), mul_smul]
  rw [integral_smul, ← meanScaledDensity_smul_posterior hM μ t x,
    smul_smul, inv_mul_cancel₀ (meanScaledDensity_pos hM μ t x).ne', one_smul]

/-- Joint observation and latent-parameter law reconstructed from the posterior. -/
def posteriorJoint (hM : 0 ≤ M) (μ : Measure (Ball d M))
    [IsProbabilityMeasure μ] (t : ℝ) : Measure (Space d × Ball d M) :=
  observationMeasure μ t ⊗ₘ posteriorKernel hM μ t

instance posteriorJoint_isProbabilityMeasure (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (posteriorJoint hM μ t) := by
  letI := observationMeasure_isProbabilityMeasure hM μ t
  unfold posteriorJoint
  infer_instance

/-- Bayes disintegration: the reconstructed joint law has exactly the Gaussian
likelihood density against Lebesgue volume times the prior. -/
theorem posteriorJoint_eq_density (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    posteriorJoint hM μ t = (volume.prod μ).withDensity
      (fun p : Space d × Ball d M => ENNReal.ofReal (phi (p.1 - t • p.2.val))) := by
  letI := observationMeasure_isProbabilityMeasure hM μ t
  have hw := (continuous_posteriorWeight hM μ t).measurable.ennreal_ofReal
  have hp := (continuous_meanScaledDensity_space μ t).measurable.ennreal_ofReal
  letI : IsSFiniteKernel ((Kernel.const (Space d) μ).withDensity
      (fun x θ => ENNReal.ofReal (posteriorWeight μ t x θ))) :=
    inferInstanceAs (IsSFiniteKernel (posteriorKernel hM μ t))
  rw [posteriorJoint, posteriorKernel, Measure.compProd_withDensity hw,
    Measure.compProd_const, observationMeasure, prod_withDensity_left hp]
  erw [← withDensity_mul _ (hp.comp measurable_fst) hw]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  change ENNReal.ofReal (meanScaledDensity μ t p.1) *
    ENNReal.ofReal (posteriorWeight μ t p.1 p.2) = _
  rw [← ENNReal.ofReal_mul (meanScaledDensity_pos hM μ t p.1).le]
  congr 1
  unfold posteriorWeight
  field_simp [(meanScaledDensity_pos hM μ t p.1).ne']

/-- The first marginal of the posterior joint law is the observation law. -/
theorem posteriorJoint_map_fst (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    (posteriorJoint hM μ t).map Prod.fst = observationMeasure μ t := by
  letI := observationMeasure_isProbabilityMeasure hM μ t
  exact Measure.fst_compProd _ _

/-- The analytic posterior mean is an actual conditional expectation with
respect to the sigma-algebra generated by the observation coordinate. -/
theorem posterior_is_conditionalExpectation (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    (posteriorJoint hM μ t)[fun p : Space d × Ball d M => p.2.val |
      (inferInstance : MeasurableSpace (Space d)).comap Prod.fst] =ᵐ[posteriorJoint hM μ t]
        fun p => meanScaledPosterior μ t p.1 := by
  letI := observationMeasure_isProbabilityMeasure hM μ t
  letI : Nonempty (Ball d M) := ⟨⟨0, by simpa using hM⟩⟩
  letI : StandardBorelSpace (Ball d M) :=
    (isClosed_le continuous_norm continuous_const).measurableSet.standardBorel
  have hY : Integrable (fun p : Space d × Ball d M => p.2.val) (posteriorJoint hM μ t) := by
    have hc : Continuous (fun p : Space d × Ball d M => p.2.val) := by fun_prop
    apply (integrable_const M : Integrable (fun _ : Space d × Ball d M => M)
      (posteriorJoint hM μ t)).mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => p.2.property
  have hk : condDistrib (Prod.snd : Space d × Ball d M → Ball d M) Prod.fst
      (posteriorJoint hM μ t) =ᵐ[observationMeasure μ t] posteriorKernel hM μ t := by
    apply Kernel.ae_eq_of_compProd_eq
    have he := compProd_map_condDistrib (μ := posteriorJoint hM μ t)
      (mβ := inferInstance) (X := Prod.fst) (Y := Prod.snd) measurable_snd.aemeasurable
    rw [posteriorJoint_map_fst] at he
    change observationMeasure μ t ⊗ₘ condDistrib Prod.snd Prod.fst (posteriorJoint hM μ t) =
      (posteriorJoint hM μ t).map id at he
    rw [Measure.map_id] at he
    exact he
  have hk' : ∀ᵐ p ∂posteriorJoint hM μ t,
      condDistrib (Prod.snd : Space d × Ball d M → Ball d M) Prod.fst
        (posteriorJoint hM μ t) p.1 = posteriorKernel hM μ t p.1 := by
    exact ae_of_ae_map (μ := posteriorJoint hM μ t) (f := Prod.fst)
      measurable_fst.aemeasurable (by rwa [posteriorJoint_map_fst])
  have hθ : StronglyMeasurable (fun θ : Ball d M => θ.val) :=
    (continuous_subtype_val : Continuous (fun θ : Ball d M => θ.val)).stronglyMeasurable
  have hce := condExp_ae_eq_integral_condDistrib (μ := posteriorJoint hM μ t)
    (X := Prod.fst) (Y := Prod.snd) measurable_fst measurable_snd.aemeasurable
    hθ hY
  filter_upwards [hce, hk'] with p hp hkx
  rw [hp, hkx, posteriorKernel_mean]

end GaussianMixturePaper
