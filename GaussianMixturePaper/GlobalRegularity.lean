import GaussianComparison.MeanScalingChiCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Global regularity and the complete divergence derivative lemma

Unlike the endpoint comparison proof, the manuscript's Lemma 1 quantifies over
all real interpolation parameters and asserts continuous differentiability.
The enlarged-radius transport and dominated-continuity argument below supply
these additional conclusions from the actual Gaussian density definitions.
-/
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

/-- Scaling into a ball whose radius also scales allows arbitrary real times. -/
def globalScalingMap {d : ℕ} {M : ℝ} (s : ℝ) : Ball d M → Ball d (|s| * M) :=
  fun θ => ⟨s • θ.val, by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left θ.property (abs_nonneg s)⟩

theorem continuous_globalScalingMap {d : ℕ} {M : ℝ} (s : ℝ) :
    Continuous (globalScalingMap (d := d) (M := M) s) := by
  unfold globalScalingMap
  fun_prop

def globalScaledPrior {d : ℕ} {M : ℝ} (μ : Measure (Ball d M)) (s : ℝ) :
    Measure (Ball d (|s| * M)) := μ.map (globalScalingMap s)

instance globalScaledPrior_isProbabilityMeasure {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) :
    IsProbabilityMeasure (globalScaledPrior μ s) :=
  Measure.isProbabilityMeasure_map (continuous_globalScalingMap s).measurable.aemeasurable

theorem meanScaledDensity_eq_globalMixture {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) (s : ℝ) :
    meanScaledDensity μ s = mixtureDensity (globalScaledPrior μ s) := by
  funext x
  have hc : Continuous (fun θ : Ball d (|s| * M) => phi (x - θ.val)) :=
    (continuous_phi d).comp (continuous_const.sub continuous_subtype_val)
  rw [mixtureDensity, globalScaledPrior,
    integral_map (continuous_globalScalingMap s).measurable.aemeasurable
      hc.aestronglyMeasurable]
  rfl

theorem integral_meanScaledDensity_global {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) :
    (∫ x, meanScaledDensity μ s x) = 1 := by
  rw [meanScaledDensity_eq_globalMixture μ s]
  exact integral_mixtureDensity _

theorem integrable_meanScaledDensity_global {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) :
    Integrable (meanScaledDensity μ s) := by
  rw [meanScaledDensity_eq_globalMixture μ s]
  exact integrable_mixtureDensity _

theorem finiteDivergences_meanScaled_global {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) :
    FiniteDivergences volume (meanScaledDensity μ s) (meanScaledDensity ν s) := by
  rw [meanScaledDensity_eq_globalMixture μ s, meanScaledDensity_eq_globalMixture ν s]
  exact finiteDivergences_mixture (mul_nonneg (abs_nonneg s) hM) _ _

/-- Continuous Gaussian integrals under uniform exponential growth on compact
parameter intervals. The domination is derived, not assumed for the integral. -/
theorem continuous_gaussian_integral {d : ℕ} {F : ℝ → Space d → ℝ}
    (hF : Continuous F.uncurry)
    (hb : ∀ T : ℝ, 0 ≤ T → ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => F s.val x)) :
    Continuous (fun s => ∫ x, phi x * F s x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := |t| + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨C, c, hC, hc, hbound⟩ := hb T hT
  apply continuousAt_of_dominated
    (bound := fun x => C * (phi x * exp (c * ‖x‖)))
  · exact Eventually.of_forall fun s =>
      ((continuous_phi d).mul (hF.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds t (by norm_num : (0 : ℝ) < 1)] with s hs
    have hsT : |s| ≤ T := by
      have hdist : |s - t| ≤ 1 := by simpa [Real.dist_eq] using hs
      have htri := abs_add_le (s - t) t
      rw [sub_add_cancel] at htri
      dsimp [T]; linarith
    filter_upwards [] with x
    rw [norm_mul, Real.norm_of_nonneg (phi_pos x).le]
    calc
      phi x * ‖F s x‖ ≤ phi x * (C * exp (c * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (hbound ⟨s, hsT⟩ x) (phi_pos x).le
      _ = _ := by ring
  · exact (integrable_phi_mul_exp_norm d c).const_mul C
  · exact Eventually.of_forall fun x =>
      (continuous_const.mul (hF.comp (continuous_id.prodMk continuous_const))).continuousAt

/-- A convenient C1 criterion retaining the explicit Gaussian derivative. -/
theorem contDiff_one_gaussian_integral {d : ℕ} {F F' : ℝ → Space d → ℝ}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ s x, HasDerivAt (fun r => F r x) (F' s x) s)
    (hb : ∀ T : ℝ, 0 ≤ T → ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => F s.val x))
    (hb' : ∀ T : ℝ, 0 ≤ T → ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => F' s.val x)) :
    ContDiff ℝ 1 (fun s => ∫ x, phi x * F s x) := by
  have hdg := hasDerivAt_gaussian_integral hF hF' hd hb hb'
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (hdg s).differentiableAt, ?_⟩
  have he : deriv (fun s => ∫ x, phi x * F s x) = (fun s => ∫ x, phi x * F' s x) :=
    funext fun s => (hdg s).deriv
  rw [he]
  exact continuous_gaussian_integral hF' hb'

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem meanScalingJeffreys_hasDerivAt_global (s : ℝ) :
    HasDerivAt (meanScalingJeffreys μ ν) (meanScalingKLRate μ ν s) s := by
  have hiμ := integrable_mul_meanScaledGap_sq hM μ ν s (integrable_meanScaledDensity_global μ s)
    (continuous_meanScaledDensity_space μ s)
  have hiν := integrable_mul_meanScaledGap_sq hM μ ν s (integrable_meanScaledDensity_global ν s)
    (continuous_meanScaledDensity_space ν s)
  convert! (meanScalingKL_hasDerivAt hM μ ν s).add (meanScalingKL_hasDerivAt hM ν μ s) using 1
  unfold meanScalingKLRate
  simp only [meanScaledGap, norm_sub_rev] at *
  rw [← mul_add, ← integral_add hiμ hiν]
  congr 1; apply integral_congr_ae; filter_upwards [] with x; ring

theorem meanScalingHellinger_eq_affinity_global :
    meanScalingHellinger μ ν =
      (fun s => 2 - 2 * affinity volume (meanScaledDensity μ s) (meanScaledDensity ν s)) := by
  funext s
  have he := (finiteDivergences_meanScaled_global hM μ ν s).hellingerSq_eq
  dsimp [meanScalingHellinger]
  linarith

theorem meanScalingHellinger_hasDerivAt_global (s : ℝ) :
    HasDerivAt (meanScalingHellinger μ ν) (meanScalingHellingerRate μ ν s) s := by
  rw [meanScalingHellinger_eq_affinity_global hM μ ν]
  convert! (hasDerivAt_const s (2 : ℝ)).sub
    ((meanScalingAffinity_hasDerivAt hM μ ν s).const_mul 2) using 1
  unfold meanScalingHellingerRate
  ring

theorem contDiff_meanScalingKL :
    ContDiff ℝ 1 (fun s => kl volume (meanScaledDensity μ s) (meanScaledDensity ν s)) := by
  simp_rw [meanScalingKL_eq_gaussian_integral μ ν]
  exact contDiff_one_gaussian_integral (continuous_scaledKLIntegrand hM μ ν)
    (continuous_scaledKLIntegrandDot hM μ ν) (scaledKLIntegrand_hasDerivAt hM μ ν)
    (fun T hT => scaledKLIntegrand_growth hM μ ν hT)
    (fun T hT => scaledKLIntegrandDot_growth hM μ ν hT)

theorem contDiff_meanScalingJeffreys : ContDiff ℝ 1 (meanScalingJeffreys μ ν) :=
  (contDiff_meanScalingKL hM μ ν).add (contDiff_meanScalingKL hM ν μ)

theorem contDiff_meanScalingAffinity :
    ContDiff ℝ 1 (fun s => affinity volume (meanScaledDensity μ s) (meanScaledDensity ν s)) := by
  simp_rw [meanScalingAffinity_eq_gaussian_integral hM μ ν]
  exact contDiff_one_gaussian_integral (continuous_scaledAffinityIntegrand μ ν)
    (continuous_scaledAffinityIntegrandDot hM μ ν) (scaledAffinityIntegrand_hasDerivAt hM μ ν)
    (fun T hT => scaledAffinityIntegrand_growth hM μ ν hT)
    (fun T hT => scaledAffinityIntegrandDot_growth hM μ ν hT)

theorem contDiff_meanScalingHellinger : ContDiff ℝ 1 (meanScalingHellinger μ ν) := by
  rw [meanScalingHellinger_eq_affinity_global hM μ ν]
  exact contDiff_const.sub (contDiff_const.mul (contDiff_meanScalingAffinity hM μ ν))

theorem contDiff_meanScalingChiSq : ContDiff ℝ 1 (meanScalingChiSq μ ν) := by
  change ContDiff ℝ 1 (fun s => meanScalingChiSq μ ν s)
  simp_rw [meanScalingChiSq_eq_gaussian_integral μ ν]
  exact contDiff_one_gaussian_integral (continuous_scaledChiIntegrand hM μ ν)
    (continuous_scaledChiIntegrandDot hM μ ν) (scaledChiIntegrand_hasDerivAt hM μ ν)
    (fun T hT => scaledChiIntegrand_growth hM μ ν hT)
    (fun T hT => scaledChiIntegrandDot_growth hM μ ν hT)

/-- Manuscript Lemma 1, including finiteness, C1 regularity on the entire real
line, and all three derivative identities at every real parameter. -/
theorem lemma1 :
    (∀ s : ℝ, FiniteDivergences volume (meanScaledDensity μ s) (meanScaledDensity ν s)) ∧
    ContDiff ℝ 1 (meanScalingJeffreys μ ν) ∧
    ContDiff ℝ 1 (meanScalingChiSq μ ν) ∧
    ContDiff ℝ 1 (meanScalingHellinger μ ν) ∧
    (∀ s : ℝ, HasDerivAt (meanScalingJeffreys μ ν) (meanScalingKLRate μ ν s) s) ∧
    (∀ s : ℝ, HasDerivAt (meanScalingChiSq μ ν) (meanScalingChiSqRate μ ν s) s) ∧
    (∀ s : ℝ, HasDerivAt (meanScalingHellinger μ ν) (meanScalingHellingerRate μ ν s) s) :=
  ⟨finiteDivergences_meanScaled_global hM μ ν,
    contDiff_meanScalingJeffreys hM μ ν, contDiff_meanScalingChiSq hM μ ν,
    contDiff_meanScalingHellinger hM μ ν, meanScalingJeffreys_hasDerivAt_global hM μ ν,
    meanScalingChiSq_hasDerivAt hM μ ν, meanScalingHellinger_hasDerivAt_global hM μ ν⟩

end GaussianComparison.GaussianModel
