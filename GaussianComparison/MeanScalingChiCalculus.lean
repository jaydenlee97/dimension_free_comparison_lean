import GaussianComparison.MeanScalingIdentities

/-! Differentiation of the actual chi-square integral. Gaussian exponential
envelopes justify differentiation, and the existing weak continuity equation
identifies the derivative with the squared posterior-mean gap. -/
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

def meanScalingChiSq {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  chiSq volume (meanScaledDensity μ s) (meanScaledDensity ν s)

def meanScalingChiSqRate {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  2 * s * ∫ x, (meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x) *
    ‖meanScaledGap μ ν s x‖ ^ 2

def scaledChiIntegrand {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  (scaledRatio μ ν s x - 1) ^ 2 * scaledPartition ν s x

def scaledChiIntegrandDot {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  2 * scaledPartitionDot μ s x * (scaledRatio μ ν s x - 1) -
    scaledPartitionDot ν s x * (scaledRatio μ ν s x ^ 2 - 1)

@[simp] theorem meanScalingChiSq_zero {d : ℕ} {M : ℝ}
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    meanScalingChiSq μ ν 0 = 0 := by simp [meanScalingChiSq]

@[simp] theorem meanScalingChiSq_one {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) :
    meanScalingChiSq μ ν 1 = chiSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  simp [meanScalingChiSq]

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem scaledRatioSquare_hasGradientAt (s : ℝ) (x : Space d) :
    HasGradientAt (fun y => scaledRatio μ ν s y ^ 2)
      ((2 * scaledRatio μ ν s x ^ 2 * s) • meanScaledGap μ ν s x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (scaledRatio_hasGradientAt hM μ ν s x).hasFDerivAt.pow 2 using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
    smul_apply, smul_eq_mul]
  norm_num
  ring

theorem scaledRatioSquare_gradient_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x =>
      (2 * scaledRatio μ ν s.val x ^ 2 * s.val) • meanScaledGap μ ν s.val x) := by
  simpa only [pow_two] using
    (((ExpGrowth.const 2).mul ((scaledRatio_growth hM hT μ ν).mul
      (scaledRatio_growth hM hT μ ν))).mul (scalingParameter_growth hT)).smul
      (meanScaledGap_growth hM μ ν hT)

theorem scaledChiIntegrand_hasDerivAt (s : ℝ) (x : Space d) :
    HasDerivAt (fun r => scaledChiIntegrand μ ν r x) (scaledChiIntegrandDot μ ν s x) s := by
  have hR := (scaledPartition_hasDerivAt μ s x).div
    (scaledPartition_hasDerivAt ν s x) (scaledPartition_pos hM ν s x).ne'
  convert! ((hR.sub_const 1).pow 2).mul (scaledPartition_hasDerivAt ν s x) using 1
  unfold scaledChiIntegrandDot scaledRatio
  dsimp only [Pi.div_apply, Pi.pow_apply]
  ring_nf
  field_simp [(scaledPartition_pos hM ν s x).ne']
  ring

theorem continuous_scaledChiIntegrand : Continuous (Function.uncurry (scaledChiIntegrand μ ν)) :=
  (((continuous_scaledRatio hM μ ν).sub continuous_const).pow 2).mul
    (continuous_scaledPartition ν)

theorem continuous_scaledChiIntegrandDot :
    Continuous (Function.uncurry (scaledChiIntegrandDot μ ν)) :=
  ((continuous_const.mul (continuous_scaledPartitionDot μ)).mul
    ((continuous_scaledRatio hM μ ν).sub continuous_const)).sub
    ((continuous_scaledPartitionDot ν).mul
      (((continuous_scaledRatio hM μ ν).pow 2).sub continuous_const))

theorem scaledChiIntegrand_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledChiIntegrand μ ν s.val x) := by
  have hR := (scaledRatio_growth hM hT μ ν).sub (ExpGrowth.const 1)
  simpa only [scaledChiIntegrand, pow_two] using (hR.mul hR).mul (scaledPartition_growth hM hT ν)

theorem scaledChiIntegrandDot_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledChiIntegrandDot μ ν s.val x) := by
  have hR := scaledRatio_growth hM hT μ ν
  simpa only [scaledChiIntegrandDot, pow_two] using
    (((ExpGrowth.const 2).mul (scaledPartitionDot_growth hM hT μ)).mul
      (hR.sub (ExpGrowth.const 1))).sub
      ((scaledPartitionDot_growth hM hT ν).mul ((hR.mul hR).sub (ExpGrowth.const 1)))

omit hM [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem meanScalingChiSq_eq_gaussian_integral (s : ℝ) :
    meanScalingChiSq μ ν s = ∫ x, phi x * scaledChiIntegrand μ ν s x := by
  unfold meanScalingChiSq chiSq
  apply integral_congr_ae
  filter_upwards [] with x
  rw [density_ratio_eq_scaledRatio μ ν, meanScaledDensity_eq_partition]
  dsimp [scaledChiIntegrand, scaledPartition]
  ring

theorem meanScalingChiSq_hasDerivAt_integral (s : ℝ) :
    HasDerivAt (meanScalingChiSq μ ν) (∫ x, phi x * scaledChiIntegrandDot μ ν s x) s := by
  change HasDerivAt (fun r => meanScalingChiSq μ ν r) _ s
  simp_rw [meanScalingChiSq_eq_gaussian_integral μ ν]
  exact hasDerivAt_gaussian_integral (continuous_scaledChiIntegrand hM μ ν)
    (continuous_scaledChiIntegrandDot hM μ ν) (scaledChiIntegrand_hasDerivAt hM μ ν)
    (fun T hT => scaledChiIntegrand_growth hM μ ν hT)
    (fun T hT => scaledChiIntegrandDot_growth hM μ ν hT) s

theorem continuous_meanScalingChiSq : Continuous (meanScalingChiSq μ ν) :=
  continuous_iff_continuousAt.mpr fun s => (meanScalingChiSq_hasDerivAt_integral hM μ ν s).continuousAt

set_option maxHeartbeats 800000 in
/-- Test the weak equation with r-1 and r²-1. Subtracting constants avoids
requiring a separate derivative-of-normalization lemma. -/
theorem meanScalingChiSq_derivative_integral (s : ℝ) :
    (∫ x, phi x * scaledChiIntegrandDot μ ν s x) = meanScalingChiSqRate μ ν s := by
  let R := scaledRatio μ ν s
  let G := fun x => (R x * s) • meanScaledGap μ ν s x
  let H := fun x => (2 * R x ^ 2 * s) • meanScaledGap μ ν s x
  have hRc : Continuous R :=
    (continuous_scaledRatio hM μ ν).comp (continuous_const.prodMk continuous_id)
  have hGc : Continuous G := (hRc.mul continuous_const).smul (continuous_meanScaledGap_space hM μ ν s)
  have hHc : Continuous H := ((continuous_const.mul (hRc.pow 2)).mul continuous_const).smul
    (continuous_meanScaledGap_space hM μ ν s)
  have hRb := fixed_growth s (fun T hT => scaledRatio_growth hM hT μ ν)
  have hR2b : ExpGrowth (fun (_ : Unit) x => R x ^ 2) := by
    simpa only [pow_two] using hRb.mul hRb
  have hGb : ExpGrowth (fun (_ : Unit) x => G x) :=
    fixed_growth (f := fun r x => (scaledRatio μ ν r x * r) • meanScaledGap μ ν r x) s
      (fun T hT => scaledRatio_gradient_growth hM μ ν hT)
  have hHb : ExpGrowth (fun (_ : Unit) x => H x) :=
    fixed_growth (f := fun r x => (2 * scaledRatio μ ν r x ^ 2 * r) • meanScaledGap μ ν r x) s
      (fun T hT => scaledRatioSquare_gradient_growth hM μ ν hT)
  have hdR (x : Space d) : HasGradientAt (fun y => R y - 1) (G x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (scaledRatio_hasGradientAt hM μ ν s x).hasFDerivAt.sub_const 1
  have hdR2 (x : Space d) : HasGradientAt (fun y => R y ^ 2 - 1) (H x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (scaledRatioSquare_hasGradientAt hM μ ν s x).hasFDerivAt.sub_const 1
  have hμ := meanScaling_weak_derivative hM μ s (fun x => R x - 1) G
    (hRc.sub continuous_const) hGc hdR (hRb.sub (ExpGrowth.const 1)) hGb
  have hν := meanScaling_weak_derivative hM ν s (fun x => R x ^ 2 - 1) H
    ((hRc.pow 2).sub continuous_const) hHc hdR2 (hR2b.sub (ExpGrowth.const 1)) hHb
  have iμ := integrable_scaledPartitionDot_mul hM μ s (hRc.sub continuous_const)
    (hRb.sub (ExpGrowth.const 1))
  have iν := integrable_scaledPartitionDot_mul hM ν s ((hRc.pow 2).sub continuous_const)
    (hR2b.sub (ExpGrowth.const 1))
  change Integrable (fun x => phi x * scaledPartitionDot μ s x * (R x - 1)) at iμ
  change Integrable (fun x => phi x * scaledPartitionDot ν s x * (R x ^ 2 - 1)) at iν
  have jμ := integrable_meanScaledDensity_mul_inner hM μ s hGc hGb
  have jν := integrable_meanScaledDensity_mul_inner hM ν s hHc hHb
  calc
    _ = 2 * (∫ x, phi x * scaledPartitionDot μ s x * (R x - 1)) -
        ∫ x, phi x * scaledPartitionDot ν s x * (R x ^ 2 - 1) := by
      rw [← integral_const_mul, ← integral_sub (iμ.const_mul 2) iν]
      apply integral_congr_ae; filter_upwards [] with x
      dsimp [scaledChiIntegrandDot, R]; ring
    _ = 2 * (∫ x, meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ) -
        ∫ x, meanScaledDensity ν s x * ⟪meanScaledPosterior ν s x, H x⟫_ℝ := by rw [hμ, hν]
    _ = ∫ x, (2 * (meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ) -
        meanScaledDensity ν s x * ⟪meanScaledPosterior ν s x, H x⟫_ℝ) := by
      rw [integral_sub (jμ.const_mul 2) jν, integral_const_mul]
    _ = meanScalingChiSqRate μ ν s := by
      unfold meanScalingChiSqRate
      rw [← integral_const_mul]
      apply integral_congr_ae; filter_upwards [] with x
      dsimp [G, H, R]
      rw [real_inner_smul_right, real_inner_smul_right]
      have hg := posterior_gap_inner μ ν s x
      rw [← hg, ← density_ratio_eq_scaledRatio μ ν]
      field_simp [(meanScaledDensity_pos hM ν s x).ne']

theorem meanScalingChiSq_hasDerivAt (s : ℝ) :
    HasDerivAt (meanScalingChiSq μ ν) (meanScalingChiSqRate μ ν s) s := by
  rw [← meanScalingChiSq_derivative_integral hM μ ν s]
  exact meanScalingChiSq_hasDerivAt_integral hM μ ν s

end GaussianComparison.GaussianModel
