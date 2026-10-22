import GaussianComparison.MeanScalingIntegration
import GaussianComparison.MeanScalingKL

/-! Differentiation of the actual KL and affinity integrals under Euclidean
volume. Uniform exponential envelopes justify every interchange. -/
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

def scaledKLIntegrand {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  scaledPartition μ s x * scaledLogRatio μ ν s x

def scaledKLIntegrandDot {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  scaledPartitionDot μ s x * (scaledLogRatio μ ν s x + 1) -
    scaledPartitionDot ν s x * scaledRatio μ ν s x

def scaledAffinityIntegrand {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  sqrt (scaledPartition μ s x) * sqrt (scaledPartition ν s x)

def scaledAffinityIntegrandDot {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  (1 / 2 : ℝ) * (scaledPartitionDot μ s x * scaledRootRatio ν μ s x +
    scaledPartitionDot ν s x * scaledRootRatio μ ν s x)

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem scaledKLIntegrand_hasDerivAt (s : ℝ) (x : Space d) :
    HasDerivAt (fun r => scaledKLIntegrand μ ν r x) (scaledKLIntegrandDot μ ν s x) s := by
  convert! (scaledPartition_hasDerivAt μ s x).mul (scaledLogRatio_hasDerivAt hM μ ν s x) using 1
  unfold scaledKLIntegrandDot scaledRatio
  have hp := (scaledPartition_pos hM μ s x).ne'
  have hq := (scaledPartition_pos hM ν s x).ne'
  field_simp
  ring

theorem scaledAffinityIntegrand_hasDerivAt (s : ℝ) (x : Space d) :
    HasDerivAt (fun r => scaledAffinityIntegrand μ ν r x)
      (scaledAffinityIntegrandDot μ ν s x) s := by
  convert! ((scaledPartition_hasDerivAt μ s x).sqrt (scaledPartition_pos hM μ s x).ne').mul
    ((scaledPartition_hasDerivAt ν s x).sqrt (scaledPartition_pos hM ν s x).ne') using 1
  unfold scaledAffinityIntegrandDot scaledRootRatio scaledRatio
  rw [sqrt_div (scaledPartition_pos hM ν s x).le,
    sqrt_div (scaledPartition_pos hM μ s x).le]
  ring

theorem continuous_scaledKLIntegrand : Continuous (Function.uncurry (scaledKLIntegrand μ ν)) :=
  (continuous_scaledPartition μ).mul (continuous_scaledLogRatio hM μ ν)

theorem continuous_scaledKLIntegrandDot : Continuous (Function.uncurry (scaledKLIntegrandDot μ ν)) :=
  ((continuous_scaledPartitionDot μ).mul ((continuous_scaledLogRatio hM μ ν).add continuous_const)).sub
    ((continuous_scaledPartitionDot ν).mul (continuous_scaledRatio hM μ ν))

omit hM in
theorem continuous_scaledAffinityIntegrand : Continuous (Function.uncurry (scaledAffinityIntegrand μ ν)) :=
  (continuous_scaledPartition μ).sqrt.mul (continuous_scaledPartition ν).sqrt

theorem continuous_scaledAffinityIntegrandDot : Continuous (Function.uncurry (scaledAffinityIntegrandDot μ ν)) :=
  continuous_const.mul (((continuous_scaledPartitionDot μ).mul (continuous_scaledRootRatio hM ν μ)).add
    ((continuous_scaledPartitionDot ν).mul (continuous_scaledRootRatio hM μ ν)))

theorem scaledKLIntegrand_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledKLIntegrand μ ν s.val x) :=
  (scaledPartition_growth hM hT μ).mul (scaledLogRatio_growth hM hT μ ν)

theorem scaledKLIntegrandDot_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledKLIntegrandDot μ ν s.val x) :=
  ((scaledPartitionDot_growth hM hT μ).mul
    ((scaledLogRatio_growth hM hT μ ν).add (ExpGrowth.const 1))).sub
    ((scaledPartitionDot_growth hM hT ν).mul (scaledRatio_growth hM hT μ ν))

theorem scaledAffinityIntegrand_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledAffinityIntegrand μ ν s.val x) :=
  (scaledPartition_growth hM hT μ).sqrt.mul (scaledPartition_growth hM hT ν).sqrt

theorem scaledAffinityIntegrandDot_growth {T : ℝ} (hT : 0 ≤ T) :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledAffinityIntegrandDot μ ν s.val x) :=
  (ExpGrowth.const (1 / 2)).mul
    (((scaledPartitionDot_growth hM hT μ).mul (scaledRootRatio_growth hM hT ν μ)).add
      ((scaledPartitionDot_growth hM hT ν).mul (scaledRootRatio_growth hM hT μ ν)))

omit hM [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem meanScalingKL_eq_gaussian_integral (s : ℝ) :
    kl volume (meanScaledDensity μ s) (meanScaledDensity ν s) =
      ∫ x, phi x * scaledKLIntegrand μ ν s x := by
  apply integral_congr_ae
  filter_upwards [] with x
  rw [density_ratio_eq_scaledRatio μ ν, meanScaledDensity_eq_partition]
  dsimp [scaledKLIntegrand, scaledLogRatio, scaledRatio, scaledPartition]
  ring

omit [IsProbabilityMeasure ν] in
theorem meanScalingAffinity_eq_gaussian_integral (s : ℝ) :
    affinity volume (meanScaledDensity μ s) (meanScaledDensity ν s) =
      ∫ x, phi x * scaledAffinityIntegrand μ ν s x := by
  apply integral_congr_ae
  filter_upwards [] with x
  rw [meanScaledDensity_eq_partition, meanScaledDensity_eq_partition]
  unfold scaledAffinityIntegrand scaledPartition
  rw [sqrt_mul (mul_pos (phi_pos _) (partition_pos hM μ _ _)).le,
    sqrt_mul (phi_pos _).le, sqrt_mul (phi_pos _).le]
  calc
    _ = sqrt (phi x) ^ 2 * (sqrt (partition μ (s • x) (s ^ 2)) *
        sqrt (partition ν (s • x) (s ^ 2))) := by ring
    _ = _ := by rw [sq_sqrt (phi_pos x).le]

theorem meanScalingKL_hasDerivAt_integral (s : ℝ) :
    HasDerivAt (fun r => kl volume (meanScaledDensity μ r) (meanScaledDensity ν r))
      (∫ x, phi x * scaledKLIntegrandDot μ ν s x) s := by
  simp_rw [meanScalingKL_eq_gaussian_integral μ ν]
  exact hasDerivAt_gaussian_integral (continuous_scaledKLIntegrand hM μ ν)
    (continuous_scaledKLIntegrandDot hM μ ν) (scaledKLIntegrand_hasDerivAt hM μ ν)
    (fun T hT => scaledKLIntegrand_growth hM μ ν hT)
    (fun T hT => scaledKLIntegrandDot_growth hM μ ν hT) s

theorem meanScalingAffinity_hasDerivAt_integral (s : ℝ) :
    HasDerivAt (fun r => affinity volume (meanScaledDensity μ r) (meanScaledDensity ν r))
      (∫ x, phi x * scaledAffinityIntegrandDot μ ν s x) s := by
  simp_rw [meanScalingAffinity_eq_gaussian_integral hM μ ν]
  exact hasDerivAt_gaussian_integral (continuous_scaledAffinityIntegrand μ ν)
    (continuous_scaledAffinityIntegrandDot hM μ ν) (scaledAffinityIntegrand_hasDerivAt hM μ ν)
    (fun T hT => scaledAffinityIntegrand_growth hM μ ν hT)
    (fun T hT => scaledAffinityIntegrandDot_growth hM μ ν hT) s

theorem continuous_meanScalingJeffreys : Continuous (meanScalingJeffreys μ ν) := by
  exact (continuous_iff_continuousAt.mpr fun s =>
    (meanScalingKL_hasDerivAt_integral hM μ ν s).continuousAt).add
    (continuous_iff_continuousAt.mpr fun s =>
      (meanScalingKL_hasDerivAt_integral hM ν μ s).continuousAt)

theorem continuous_meanScalingAffinity :
    Continuous (fun s => affinity volume (meanScaledDensity μ s) (meanScaledDensity ν s)) :=
  continuous_iff_continuousAt.mpr fun s =>
    (meanScalingAffinity_hasDerivAt_integral hM μ ν s).continuousAt

theorem continuousOn_meanScalingHellinger : ContinuousOn (meanScalingHellinger μ ν) (Icc 0 1) := by
  apply ((show Continuous (fun _ : ℝ => (2 : ℝ)) from continuous_const).sub
    ((continuous_meanScalingAffinity hM μ ν).const_mul 2)).continuousOn.congr
  intro s hs
  have ha : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have he := (finiteDivergences_meanScaled hM μ ν s ha).hellingerSq_eq
  dsimp [meanScalingHellinger]
  linarith

end GaussianComparison.GaussianModel
