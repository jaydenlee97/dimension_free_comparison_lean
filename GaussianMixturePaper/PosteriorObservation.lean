import GaussianMixturePaper.ObservationLaw
import GaussianMixturePaper.PosteriorModel
import Mathlib.Probability.Independence.Basic

/-!
# Conditional means on the independent Gaussian observation model

The prior and Gaussian noise are independent on the product probability space.
The posterior vector used in the paper is the conditional expectation of the
original prior vector given `t • θ + z`, with no posterior identity assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open GaussianComparison.GaussianModel

namespace GaussianMixturePaper
variable {d : ℕ} {M : ℝ}

/-- The original mixing vector and standard Gaussian noise are independent. -/
theorem priorVector_independent_noise
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    IndepFun (fun p : Ball d M × Space d => p.1.val) Prod.snd
      (μ.prod (gaussianNoise d)) := by
  exact indepFun_prod (μ := μ) (ν := gaussianNoise d)
    (X := fun θ : Ball d M => θ.val) (Y := id) measurable_subtype_coe measurable_id

/-- Equation (2.3), interpreted literally as a conditional expectation on the
independent product model `Θ ~ μ`, `Z ~ N(0,I)`, `X = tΘ + Z`. -/
theorem posterior_is_conditionalExpectation_independent (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) :
    (μ.prod (gaussianNoise d))[fun p : Ball d M × Space d => p.1.val |
      (inferInstance : MeasurableSpace (Space d)).comap
        (fun p : Ball d M × Space d => t • p.1.val + p.2)]
      =ᵐ[μ.prod (gaussianNoise d)]
        fun p => meanScaledPosterior μ t (t • p.1.val + p.2) := by
  letI := observationMeasure_isProbabilityMeasure hM μ t
  letI : Nonempty (Ball d M) := ⟨⟨0, by simpa using hM⟩⟩
  letI : StandardBorelSpace (Ball d M) :=
    (isClosed_le continuous_norm continuous_const).measurableSet.standardBorel
  let P := μ.prod (gaussianNoise d)
  let X := fun p : Ball d M × Space d => t • p.1.val + p.2
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hjoint : P.map (fun p => (X p, p.1)) = posteriorJoint hM μ t :=
    (independent_observation_joint_density μ t).trans (posteriorJoint_eq_density hM μ t).symm
  have hXlaw : P.map X = observationMeasure μ t := by
    have hf := Measure.fst_map_prodMk (μ := P) (X := X) (Y := Prod.fst) measurable_fst
    rw [hjoint] at hf
    exact hf.symm.trans (posteriorJoint_map_fst hM μ t)
  have hY : Integrable (fun p : Ball d M × Space d => p.1.val) P := by
    have hc : Continuous (fun p : Ball d M × Space d => p.1.val) := by fun_prop
    apply (integrable_const M : Integrable (fun _ : Ball d M × Space d => M) P).mono'
      hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => p.1.property
  have hk : condDistrib (Prod.fst : Ball d M × Space d → Ball d M) X P
      =ᵐ[observationMeasure μ t] posteriorKernel hM μ t := by
    apply Kernel.ae_eq_of_compProd_eq
    have he := compProd_map_condDistrib (μ := P) (mβ := inferInstance)
      (X := X) (Y := Prod.fst) measurable_fst.aemeasurable
    rw [hXlaw, hjoint] at he
    exact he
  have hk' : ∀ᵐ p ∂P, condDistrib (Prod.fst : Ball d M × Space d → Ball d M) X P (X p)
      = posteriorKernel hM μ t (X p) :=
    ae_of_ae_map (μ := P) (f := X) hX.aemeasurable (by rwa [hXlaw])
  have hθ : StronglyMeasurable (fun θ : Ball d M => θ.val) :=
    (continuous_subtype_val : Continuous (fun θ : Ball d M => θ.val)).stronglyMeasurable
  have hce := condExp_ae_eq_integral_condDistrib (μ := P) (X := X) (Y := Prod.fst)
    hX measurable_fst.aemeasurable hθ hY
  filter_upwards [hce, hk'] with p hp hkx
  rw [hp, hkx, posteriorKernel_mean]

end GaussianMixturePaper
