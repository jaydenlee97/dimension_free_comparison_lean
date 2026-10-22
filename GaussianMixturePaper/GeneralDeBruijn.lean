import GaussianMixturePaper.FisherMatrix

set_option maxHeartbeats 800000

/-!
# A general generator identity for the actual Gaussian interpolation

The hypotheses below state differentiability on positive arguments and local
exponential growth of the generator and its first two derivatives composed with
the likelihood ratio. They do not assume a divergence derivative or integration-
by-parts identity. Such growth assumptions are necessary: arbitrary C² convex
generators need not have finite divergence even for Gaussian densities.
-/
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

/-- C² regularity on positive arguments, allowing singular derivatives at zero. -/
structure PositiveC2Generator (f : ℝ → ℝ) : Prop where
  first : ∀ r, 0 < r → HasDerivAt f (deriv f r) r
  second : ∀ r, 0 < r → HasDerivAt (deriv f) (deriv (deriv f) r) r
  continuous_second : ContinuousOn (deriv (deriv f)) (Ioi 0)

/-- Uniform-in-time exponential growth on every compact time interval. -/
structure LocalGeneratorGrowth {d : ℕ} {M : ℝ}
    (μ ν : Measure (Ball d M)) (f : ℝ → ℝ) : Prop where
  value : ∀ T : ℝ, 0 ≤ T → ExpGrowth
    (fun (s : {s : ℝ // |s| ≤ T}) x => f (scaledRatio μ ν s.val x))
  first : ∀ T : ℝ, 0 ≤ T → ExpGrowth
    (fun (s : {s : ℝ // |s| ≤ T}) x => deriv f (scaledRatio μ ν s.val x))
  second : ∀ T : ℝ, 0 ≤ T → ExpGrowth
    (fun (s : {s : ℝ // |s| ≤ T}) x => deriv (deriv f) (scaledRatio μ ν s.val x))

namespace PositiveC2Generator
variable {f : ℝ → ℝ} (hf : PositiveC2Generator f)
include hf

theorem continuous_value : ContinuousOn f (Ioi 0) :=
  fun r hr => (hf.first r hr).continuousAt.continuousWithinAt

theorem continuous_first : ContinuousOn (deriv f) (Ioi 0) :=
  fun r hr => (hf.second r hr).continuousAt.continuousWithinAt

theorem compensated_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun z => f z - z * deriv f z) (-r * deriv (deriv f) r) r := by
  convert! (hf.first r hr).sub ((hasDerivAt_id r).mul (hf.second r hr)) using 1
  simp only [id_eq]
  ring
end PositiveC2Generator

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem continuous_generator_ratio {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0)) :
    Continuous (fun p : ℝ × Space d => f (scaledRatio μ ν p.1 p.2)) :=
  hf.comp_continuous (continuous_scaledRatio hM μ ν)
    (fun p => scaledRatio_pos hM μ ν p.1 p.2)

theorem generator_ratio_hasGradientAt {f : ℝ → ℝ} (s : ℝ) (x : Space d)
    {f' : ℝ} (hf : HasDerivAt f f' (scaledRatio μ ν s x)) :
    HasGradientAt (fun y => f (scaledRatio μ ν s y))
      ((f' * (scaledRatio μ ν s x * s)) •
        meanScaledGap μ ν s x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := hf.comp_hasFDerivAt x (scaledRatio_hasGradientAt hM μ ν s x).hasFDerivAt
  convert! h using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
    smul_apply, smul_eq_mul]
  ring

/-- The Gaussian-base density integrand for a general generator. -/
def generalFIntegrand (f : ℝ → ℝ) (s : ℝ) (x : Space d) : ℝ :=
  scaledPartition ν s x * f (scaledRatio μ ν s x)

/-- Its ordinary time derivative, computed by the product and quotient rules. -/
def generalFIntegrandDot (f : ℝ → ℝ) (s : ℝ) (x : Space d) : ℝ :=
  scaledPartitionDot μ s x * deriv f (scaledRatio μ ν s x) +
    scaledPartitionDot ν s x *
      (f (scaledRatio μ ν s x) - scaledRatio μ ν s x * deriv f (scaledRatio μ ν s x))

theorem generalFIntegrand_hasDerivAt {f : ℝ → ℝ} (hf : PositiveC2Generator f)
    (s : ℝ) (x : Space d) :
    HasDerivAt (fun r => generalFIntegrand μ ν f r x) (generalFIntegrandDot μ ν f s x) s := by
  have hr := (scaledPartition_hasDerivAt μ s x).div (scaledPartition_hasDerivAt ν s x)
    (scaledPartition_pos hM ν s x).ne'
  have h := (scaledPartition_hasDerivAt ν s x).mul
    ((hf.first _ (scaledRatio_pos hM μ ν s x)).comp s hr)
  convert! h using 1
  unfold generalFIntegrandDot scaledRatio
  simp only [Function.comp_apply, Pi.div_apply]
  field_simp [(scaledPartition_pos hM ν s x).ne']
  ring

theorem generalFIntegrand_continuous {f : ℝ → ℝ} (hf : PositiveC2Generator f) :
    Continuous (generalFIntegrand μ ν f).uncurry :=
  (continuous_scaledPartition ν).mul (continuous_generator_ratio hM μ ν hf.continuous_value)

theorem generalFIntegrandDot_continuous {f : ℝ → ℝ} (hf : PositiveC2Generator f) :
    Continuous (generalFIntegrandDot μ ν f).uncurry :=
  ((continuous_scaledPartitionDot μ).mul (continuous_generator_ratio hM μ ν hf.continuous_first)).add
    ((continuous_scaledPartitionDot ν).mul
      ((continuous_generator_ratio hM μ ν hf.continuous_value).sub
        ((continuous_scaledRatio hM μ ν).mul (continuous_generator_ratio hM μ ν hf.continuous_first))))

omit [IsProbabilityMeasure μ] in
theorem generalFIntegrand_growth {f : ℝ → ℝ} (hg : LocalGeneratorGrowth μ ν f)
    {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => generalFIntegrand μ ν f s.val x) :=
  (scaledPartition_growth hM hT ν).mul (hg.value T hT)

theorem generalFIntegrandDot_growth {f : ℝ → ℝ} (hg : LocalGeneratorGrowth μ ν f)
    {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => generalFIntegrandDot μ ν f s.val x) :=
  ((scaledPartitionDot_growth hM hT μ).mul (hg.first T hT)).add
    ((scaledPartitionDot_growth hM hT ν).mul
      ((hg.value T hT).sub ((scaledRatio_growth hM hT μ ν).mul (hg.first T hT))))

omit hM [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem densityFDivergence_eq_generalFIntegrand (f : ℝ → ℝ) (s : ℝ) :
    densityFDivergence volume (meanScaledDensity μ s) (meanScaledDensity ν s) f =
      ∫ x, phi x * generalFIntegrand μ ν f s x := by
  unfold densityFDivergence
  apply integral_congr_ae
  filter_upwards [] with x
  rw [density_ratio_eq_scaledRatio, meanScaledDensity_eq_partition]
  unfold generalFIntegrand scaledPartition
  ring

theorem generalFDivergence_hasDerivAt_integral {f : ℝ → ℝ}
    (hf : PositiveC2Generator f) (hg : LocalGeneratorGrowth μ ν f) (s : ℝ) :
    HasDerivAt (fun r => densityFDivergence volume (meanScaledDensity μ r)
      (meanScaledDensity ν r) f) (∫ x, phi x * generalFIntegrandDot μ ν f s x) s := by
  simp_rw [densityFDivergence_eq_generalFIntegrand μ ν]
  exact hasDerivAt_gaussian_integral (generalFIntegrand_continuous hM μ ν hf)
    (generalFIntegrandDot_continuous hM μ ν hf) (generalFIntegrand_hasDerivAt hM μ ν hf)
    (fun T hT => generalFIntegrand_growth hM μ ν hg hT)
    (fun T hT => generalFIntegrandDot_growth hM μ ν hg hT) s

/-- Absolute integrability of the genuine f-divergence integrand. -/
theorem integrable_generalFDivergence {f : ℝ → ℝ}
    (hf : PositiveC2Generator f) (hg : LocalGeneratorGrowth μ ν f) (s : ℝ) :
    Integrable (fun x => meanScaledDensity ν s x *
      f (meanScaledDensity μ s x / meanScaledDensity ν s x)) := by
  have hc : Continuous (generalFIntegrand μ ν f s) :=
    (generalFIntegrand_continuous hM μ ν hf).comp (continuous_const.prodMk continuous_id)
  have hb : ExpGrowth (fun (_ : Unit) x => generalFIntegrand μ ν f s x) :=
    fixed_growth (f := generalFIntegrand μ ν f) s
      (fun T hT => generalFIntegrand_growth hM μ ν hg hT)
  apply (hb.gaussian_integrable () hc.aestronglyMeasurable).congr
  filter_upwards [] with x
  rw [density_ratio_eq_scaledRatio, meanScaledDensity_eq_partition]
  unfold generalFIntegrand scaledPartition
  ring

/-- Continuous differentiability follows from the same local domination bounds. -/
theorem generalFDivergence_contDiff_one {f : ℝ → ℝ}
    (hf : PositiveC2Generator f) (hg : LocalGeneratorGrowth μ ν f) :
    ContDiff ℝ 1 (fun r => densityFDivergence volume (meanScaledDensity μ r)
      (meanScaledDensity ν r) f) := by
  simp_rw [densityFDivergence_eq_generalFIntegrand μ ν]
  exact contDiff_one_gaussian_integral (generalFIntegrand_continuous hM μ ν hf)
    (generalFIntegrandDot_continuous hM μ ν hf) (generalFIntegrand_hasDerivAt hM μ ν hf)
    (fun T hT => generalFIntegrand_growth hM μ ν hg hT)
    (fun T hT => generalFIntegrandDot_growth hM μ ν hg hT)

/-- Integration by parts turns the time derivative into the general posterior
energy. Both test functions and their gradients have proved integrability. -/
theorem generalFDivergence_derivative_integral {f : ℝ → ℝ}
    (hf : PositiveC2Generator f) (hg : LocalGeneratorGrowth μ ν f) (s : ℝ) :
    (∫ x, phi x * generalFIntegrandDot μ ν f s x) =
      s * ∫ x, meanScaledDensity ν s x * (scaledRatio μ ν s x) ^ 2 *
        deriv (deriv f) (scaledRatio μ ν s x) * ‖meanScaledGap μ ν s x‖ ^ 2 := by
  let R := scaledRatio μ ν s
  let A := fun x => deriv f (R x)
  let B := fun x => f (R x) - R x * deriv f (R x)
  let G := fun x => (s * R x * deriv (deriv f) (R x)) • meanScaledGap μ ν s x
  let H := fun x => (-s * (R x) ^ 2 * deriv (deriv f) (R x)) • meanScaledGap μ ν s x
  have hRc : Continuous R :=
    (continuous_scaledRatio hM μ ν).comp (continuous_const.prodMk continuous_id)
  have hAc : Continuous A := hf.continuous_first.comp_continuous hRc
    (fun x => scaledRatio_pos hM μ ν s x)
  have hFc : Continuous (fun x => f (R x)) := hf.continuous_value.comp_continuous hRc
    (fun x => scaledRatio_pos hM μ ν s x)
  have hCc : Continuous (fun x => deriv (deriv f) (R x)) :=
    hf.continuous_second.comp_continuous hRc (fun x => scaledRatio_pos hM μ ν s x)
  have hBc : Continuous B := hFc.sub (hRc.mul hAc)
  have hGc : Continuous G := ((continuous_const.mul hRc).mul hCc).smul
    (continuous_meanScaledGap_space hM μ ν s)
  have hHc : Continuous H := ((continuous_const.mul (hRc.pow 2)).mul hCc).smul
    (continuous_meanScaledGap_space hM μ ν s)
  have hRb := fixed_growth s (fun T hT => scaledRatio_growth hM hT μ ν)
  have hAb := fixed_growth (f := fun r x => deriv f (scaledRatio μ ν r x)) s hg.first
  have hFb := fixed_growth (f := fun r x => f (scaledRatio μ ν r x)) s hg.value
  have hCb := fixed_growth (f := fun r x => deriv (deriv f) (scaledRatio μ ν r x)) s hg.second
  have hBb := hFb.sub (hRb.mul hAb)
  have hgap := fixed_growth s (fun T hT => meanScaledGap_growth hM μ ν hT)
  have hGb : ExpGrowth (fun (_ : Unit) x => G x) :=
    (((ExpGrowth.const s).mul hRb).mul hCb).smul hgap
  have hHb : ExpGrowth (fun (_ : Unit) x => H x) := by
    simpa only [H, R, pow_two] using
      (((ExpGrowth.const (-s)).mul (hRb.mul hRb)).mul hCb).smul hgap
  have hdA (x : Space d) : HasGradientAt A (G x) x := by
    convert! generator_ratio_hasGradientAt hM μ ν s x
      (hf.second _ (scaledRatio_pos hM μ ν s x)) using 1
    dsimp [G, R]
    congr 1
    ring
  have hdB (x : Space d) : HasGradientAt B (H x) x := by
    convert! generator_ratio_hasGradientAt hM μ ν s x
      (hf.compensated_hasDerivAt (scaledRatio_pos hM μ ν s x)) using 1
    dsimp [H, R]
    congr 1
    ring
  have hμ := meanScaling_weak_derivative hM μ s A G hAc hGc hdA hAb hGb
  have hν := meanScaling_weak_derivative hM ν s B H hBc hHc hdB hBb hHb
  have iμ := integrable_scaledPartitionDot_mul hM μ s hAc hAb
  have iν := integrable_scaledPartitionDot_mul hM ν s hBc hBb
  have jμ := integrable_meanScaledDensity_mul_inner hM μ s hGc hGb
  have jν := integrable_meanScaledDensity_mul_inner hM ν s hHc hHb
  calc
    _ = (∫ x, phi x * scaledPartitionDot μ s x * A x) +
        ∫ x, phi x * scaledPartitionDot ν s x * B x := by
      rw [← integral_add iμ iν]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [generalFIntegrandDot, A, B, R]
      ring
    _ = (∫ x, meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ) +
        ∫ x, meanScaledDensity ν s x * ⟪meanScaledPosterior ν s x, H x⟫_ℝ := by rw [hμ, hν]
    _ = ∫ x, (meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ +
        meanScaledDensity ν s x * ⟪meanScaledPosterior ν s x, H x⟫_ℝ) :=
      (integral_add jμ jν).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [G, H, R]
      rw [real_inner_smul_right, real_inner_smul_right]
      have hr := meanScaledDensity_mul_ratio hM μ ν s x
      have hgap := posterior_gap_inner μ ν s x
      rw [← hgap, ← hr]
      ring

/-- Actual general f-divergence derivative under explicit regularity and growth. -/
theorem generalFDivergence_hasDerivAt {f : ℝ → ℝ}
    (hf : PositiveC2Generator f) (hg : LocalGeneratorGrowth μ ν f) (s : ℝ) :
    HasDerivAt (fun r => densityFDivergence volume (meanScaledDensity μ r)
      (meanScaledDensity ν r) f)
      (s * ∫ x, meanScaledDensity ν s x * (scaledRatio μ ν s x) ^ 2 *
        deriv (deriv f) (scaledRatio μ ν s x) * ‖meanScaledGap μ ν s x‖ ^ 2) s := by
  rw [← generalFDivergence_derivative_integral hM μ ν hf hg s]
  exact generalFDivergence_hasDerivAt_integral hM μ ν hf hg s

/-- The generator's Fisher weight is integrable and continuous under the stated
hypotheses. This is proved from exponential Gaussian domination. -/
theorem general_generatorDensityWeight_regular {f : ℝ → ℝ}
    (hf : PositiveC2Generator f) (hg : LocalGeneratorGrowth μ ν f) (s : ℝ) :
    Integrable (generatorDensityWeight μ ν s f) ∧ Continuous (generatorDensityWeight μ ν s f) := by
  let W : ℝ → Space d → ℝ := fun t x =>
    scaledPartition ν t x * (scaledRatio μ ν t x * scaledRatio μ ν t x) *
      deriv (deriv f) (scaledRatio μ ν t x)
  have hgc : Continuous (fun p : ℝ × Space d => deriv (deriv f) (scaledRatio μ ν p.1 p.2)) :=
    continuous_generator_ratio hM μ ν hf.continuous_second
  have hWc : Continuous W.uncurry :=
    ((continuous_scaledPartition ν).mul
      ((continuous_scaledRatio hM μ ν).mul (continuous_scaledRatio hM μ ν))).mul hgc
  have hWg (T : ℝ) (hT : 0 ≤ T) :
      ExpGrowth (fun (t : {t : ℝ // |t| ≤ T}) x => W t.val x) :=
    ((scaledPartition_growth hM hT ν).mul
      ((scaledRatio_growth hM hT μ ν).mul (scaledRatio_growth hM hT μ ν))).mul (hg.second T hT)
  have hWs : Continuous (W s) :=
    hWc.comp (continuous_const.prodMk continuous_id)
  have hWb : ExpGrowth (fun (_ : Unit) x => W s x) := fixed_growth (f := W) s hWg
  have he : generatorDensityWeight μ ν s f = fun x => phi x * W s x := by
    funext x
    unfold generatorDensityWeight
    rw [density_ratio_eq_scaledRatio, meanScaledDensity_eq_partition]
    dsimp [W, scaledPartition]
    ring
  rw [he]
  exact ⟨hWb.gaussian_integrable () hWs.aestronglyMeasurable,
    (continuous_phi d).mul hWs⟩

/-- Equation (3.3) for a general admissible generator, with the actual matrix
trace. All differentiation and integration by parts are derived in this file. -/
theorem general_deBruijn_matrix {f : ℝ → ℝ}
    (hf : PositiveC2Generator f) (hg : LocalGeneratorGrowth μ ν f) (s : ℝ) :
    s * deriv (fun r => densityFDivergence volume (meanScaledDensity μ r)
      (meanScaledDensity ν r) f) s = Matrix.trace (generatorFisherMatrix μ ν s f) := by
  obtain ⟨hi, hc⟩ := general_generatorDensityWeight_regular hM μ ν hf hg s
  have htrace : Matrix.trace (generatorFisherMatrix μ ν s f) =
      scoreFisherTrace μ ν s (generatorDensityWeight μ ν s f) :=
    scoreFisherMatrix_trace hM μ ν hi hc
  rw [(generalFDivergence_hasDerivAt hM μ ν hf hg s).deriv,
    htrace, scoreFisherTrace_eq hM μ ν]
  unfold generatorDensityWeight
  simp_rw [density_ratio_eq_scaledRatio]
  ring

end GaussianComparison.GaussianModel
