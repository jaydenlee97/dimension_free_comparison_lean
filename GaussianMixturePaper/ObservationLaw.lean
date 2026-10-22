import GaussianMixturePaper.PosteriorModel
import Mathlib.MeasureTheory.Group.Integral

/-! The independent Gaussian observation model, transported to the joint
observation/prior density by a translation in each prior fiber. -/
noncomputable section
open MeasureTheory Real
open GaussianComparison.GaussianModel

namespace GaussianMixturePaper
variable {d : ℕ} {M : ℝ}

/-- Standard Gaussian noise specified by its normalized Lebesgue density. -/
def gaussianNoise (d : ℕ) : Measure (Space d) :=
  volume.withDensity (fun z => ENNReal.ofReal (phi z))

instance gaussianNoise_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (gaussianNoise d) := by
  constructor
  rw [gaussianNoise, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_phi d)
      (Filter.Eventually.of_forall fun x => (phi_pos x).le), integral_phi]
  simp

/-- The observation and original prior vector on the independent product model. -/
def observationPair (t : ℝ) (p : Ball d M × Space d) : Space d × Ball d M :=
  (t • p.1.val + p.2, p.1)

/-- Translation of the independent product law gives the exact joint density. -/
theorem independent_observation_joint_density
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    (μ.prod (gaussianNoise d)).map (observationPair t) =
      (volume.prod μ).withDensity
        (fun p : Space d × Ball d M => ENNReal.ofReal (phi (p.1 - t • p.2.val))) := by
  have hm : Measurable (observationPair (d := d) (M := M) t) := by
    unfold observationPair
    fun_prop
  have hg : Measurable (fun z : Space d => ENNReal.ofReal (phi z)) := by
    unfold phi
    fun_prop
  have hk : Measurable (fun p : Space d × Ball d M =>
      ENNReal.ofReal (phi (p.1 - t • p.2.val))) := by
    unfold phi
    fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm]
  erw [lintegral_prod _ (hf.comp hm).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀ hk.aemeasurable hf.aemeasurable,
    lintegral_prod_symm _ (hk.mul hf).aemeasurable]
  apply lintegral_congr
  intro θ
  have hfθ : Measurable (fun y : Space d => f (observationPair t (θ, y))) :=
    hf.comp (by unfold observationPair; fun_prop)
  erw [gaussianNoise, lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable
    hfθ.aemeasurable]
  have he := lintegral_add_left_eq_self
    (μ := (volume : Measure (Space d)))
    (fun x => ENNReal.ofReal (phi (x - t • θ.val)) * f (x, θ)) (t • θ.val)
  simpa [observationPair] using he

/-- The independent-noise construction and the posterior-kernel joint law agree. -/
theorem independent_observation_eq_posteriorJoint (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    (μ.prod (gaussianNoise d)).map (observationPair t) = posteriorJoint hM μ t := by
  rw [independent_observation_joint_density, posteriorJoint_eq_density]

/-- The law of `t Θ + Z` is exactly the Gaussian-mixture density in (2.1). -/
theorem independent_observation_law (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    (μ.prod (gaussianNoise d)).map
      (fun p : Ball d M × Space d => t • p.1.val + p.2) = observationMeasure μ t := by
  have hm : Measurable (observationPair (d := d) (M := M) t) := by
    unfold observationPair
    fun_prop
  have he := congrArg (Measure.map (Prod.fst : Space d × Ball d M → Space d))
    (independent_observation_eq_posteriorJoint hM μ t)
  rw [Measure.map_map measurable_fst hm, posteriorJoint_map_fst] at he
  exact he

end GaussianMixturePaper
