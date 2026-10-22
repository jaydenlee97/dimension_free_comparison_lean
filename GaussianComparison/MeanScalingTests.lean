import GaussianComparison.MeanScalingBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open MeasureTheory Real Filter
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem scaledRatio_pos (s : ℝ) (x : Space d) : 0 < scaledRatio μ ν s x :=
  div_pos (scaledPartition_pos hM μ s x) (scaledPartition_pos hM ν s x)

omit hM [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem density_ratio_eq_scaledRatio (s : ℝ) (x : Space d) :
    meanScaledDensity μ s x / meanScaledDensity ν s x = scaledRatio μ ν s x := by
  rw [meanScaledDensity_eq_partition, meanScaledDensity_eq_partition]
  exact mul_div_mul_left _ _ (phi_pos x).ne'

theorem continuous_scaledRatio : Continuous (Function.uncurry (scaledRatio μ ν)) :=
  (continuous_scaledPartition μ).div (continuous_scaledPartition ν)
    (fun p => (scaledPartition_pos hM ν p.1 p.2).ne')

theorem continuous_scaledLogRatio : Continuous (Function.uncurry (scaledLogRatio μ ν)) :=
  (continuous_scaledRatio hM μ ν).log (fun p => (scaledRatio_pos hM μ ν p.1 p.2).ne')

theorem continuous_scaledRootRatio : Continuous (Function.uncurry (scaledRootRatio μ ν)) :=
  (continuous_scaledRatio hM μ ν).sqrt

theorem scaledLogRatio_hasDerivAt (s : ℝ) (x : Space d) :
    HasDerivAt (fun r => scaledLogRatio μ ν r x)
      (scaledPartitionDot μ s x / scaledPartition μ s x -
        scaledPartitionDot ν s x / scaledPartition ν s x) s := by
  convert! ((scaledPartition_hasDerivAt μ s x).log (scaledPartition_pos hM μ s x).ne').sub
    ((scaledPartition_hasDerivAt ν s x).log (scaledPartition_pos hM ν s x).ne') using 1
  funext r
  exact Real.log_div (scaledPartition_pos hM μ r x).ne' (scaledPartition_pos hM ν r x).ne'

theorem scaledLogRatio_hasGradientAt (s : ℝ) (x : Space d) :
    HasGradientAt (scaledLogRatio μ ν s) (s • meanScaledGap μ ν s x) x := by
  convert! log_meanScaledDensity_ratio_hasGradientAt hM μ ν s x using 1
  funext y
  rw [density_ratio_eq_scaledRatio μ ν]
  rfl

theorem scaledRatio_hasGradientAt (s : ℝ) (x : Space d) :
    HasGradientAt (scaledRatio μ ν s)
      ((scaledRatio μ ν s x * s) • meanScaledGap μ ν s x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (scaledLogRatio_hasGradientAt hM μ ν s x).hasFDerivAt.exp
  convert! h using 1
  · funext y; exact (Real.exp_log (scaledRatio_pos hM μ ν s y)).symm
  · ext v
    have he : exp (scaledLogRatio μ ν s x) = scaledRatio μ ν s x :=
      Real.exp_log (scaledRatio_pos hM μ ν s x)
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, smul_eq_mul, he]
    ring

theorem scaledRootRatio_eq_exp (s : ℝ) (x : Space d) :
    scaledRootRatio μ ν s x = exp (scaledLogRatio μ ν s x / 2) := by
  rw [scaledRootRatio, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (scaledRatio_pos hM μ ν s x)]
  congr 1
  unfold scaledLogRatio scaledRatio
  ring

theorem scaledRootRatio_hasGradientAt (s : ℝ) (x : Space d) :
    HasGradientAt (scaledRootRatio μ ν s)
      ((s / 2 * scaledRootRatio μ ν s x) • meanScaledGap μ ν s x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((scaledLogRatio_hasGradientAt hM μ ν s x).hasFDerivAt.const_smul (1 / 2 : ℝ)).exp
  convert! h using 1
  · funext y
    dsimp
    rw [scaledRootRatio_eq_exp hM μ ν s y]
    congr 1; ring
  · ext v
    have he : exp ((1 / 2 : ℝ) * scaledLogRatio μ ν s x) = scaledRootRatio μ ν s x := by
      rw [scaledRootRatio_eq_exp hM μ ν s x]; congr 1; ring
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, Pi.smul_apply, smul_eq_mul, he]
    ring

theorem meanScaledPosterior_growth {T : ℝ} (_hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => meanScaledPosterior μ s.val x) :=
  ExpGrowth.of_bounded M hM (fun s x => norm_meanScaledPosterior_le hM μ s.val x)

theorem meanScaledGap_growth {T : ℝ} (_hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => meanScaledGap μ ν s.val x) :=
  ExpGrowth.of_bounded (2 * M) (by positivity) (fun s x => norm_meanScaledGap_le hM μ ν s.val x)

omit hM μ ν [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem scalingParameter_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) (_ : Space d) => s.val) :=
  ExpGrowth.of_bounded T hT (fun s _ => s.property)

theorem scaledLogRatio_gradient_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => s.val • meanScaledGap μ ν s.val x) :=
  (scalingParameter_growth (d := d) hT).smul (meanScaledGap_growth hM μ ν hT)

theorem scaledRatio_gradient_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x =>
      (scaledRatio μ ν s.val x * s.val) • meanScaledGap μ ν s.val x) :=
  ((scaledRatio_growth hM hT μ ν).mul (scalingParameter_growth hT)).smul
    (meanScaledGap_growth hM μ ν hT)

theorem scaledRootRatio_gradient_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x =>
      (s.val / 2 * scaledRootRatio μ ν s.val x) • meanScaledGap μ ν s.val x) := by
  simpa only [div_eq_mul_inv, one_mul] using
    (((scalingParameter_growth hT).mul (ExpGrowth.const (1 / 2))).mul
      (scaledRootRatio_growth hM hT μ ν)).smul (meanScaledGap_growth hM μ ν hT)

end GaussianComparison.GaussianModel
