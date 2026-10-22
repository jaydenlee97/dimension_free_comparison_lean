import GaussianComparison.GaussianSmooth
import GaussianComparison.GaussianFiniteDivergences
import GaussianComparison.ElementaryKLCore

/-!
# Interpolation for the elementary KL proof by scaling the mixing means

The new density is the actual integral `∫ θ, phi (x - s • θ.val) ∂μ`.
We reuse the existing partition, posterior means, compact-prior calculus,
Gaussian normalization, and finite-divergence results. This file proves
the density bridge, endpoints, normalization, finiteness and bounded gap.
The divergence identities are proved in `MeanScalingIdentities.lean`.
-/

noncomputable section

open MeasureTheory Real Set
open scoped InnerProductSpace

namespace GaussianComparison.GaussianModel

/-- Fixed Gaussian noise, with each mixing mean multiplied by `s`. -/
def meanScaledDensity {d : ℕ} {M : ℝ} (μ : Measure (Ball d M))
    (s : ℝ) (x : Space d) : ℝ :=
  ∫ θ, phi (x - s • θ.val) ∂μ

/-- The weighted mean of the original (unscaled) mixing vectors. -/
def meanScaledPosterior {d : ℕ} {M : ℝ} (μ : Measure (Ball d M))
    (s : ℝ) (x : Space d) : Space d :=
  posteriorMean μ (s • x) (s ^ 2)

def meanScaledGap {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M))
    (s : ℝ) (x : Space d) : Space d :=
  meanScaledPosterior μ s x - meanScaledPosterior ν s x

/-- Scaling a mean is equivalent to scaling space and squaring partition time. -/
theorem kernel_mean_scaling {d : ℕ} (θ x : Space d) (s : ℝ) :
    kernel θ (s • x) (s ^ 2) = kernel (s • θ) x 1 := by
  unfold kernel
  congr 1
  rw [real_inner_smul_right, real_inner_smul_left, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem phi_mul_kernel_mean_scaling {d : ℕ} (θ x : Space d) (s : ℝ) :
    phi x * kernel θ (s • x) (s ^ 2) = phi (x - s • θ) := by
  rw [kernel_mean_scaling, phi_mul_kernel]

/-- Reuse the existing actual partition instead of defining another one. -/
theorem meanScaledDensity_eq_partition {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) (s : ℝ) (x : Space d) :
    meanScaledDensity μ s x = phi x * partition μ (s • x) (s ^ 2) := by
  rw [partition, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ =>
    (phi_mul_kernel_mean_scaling θ.val x s).symm

/-- Ordinary differentiation of one scaled Gaussian; no space-time process. -/
theorem phi_mean_scaling_hasDerivAt {d : ℕ} (θ x : Space d) (s : ℝ) :
    HasDerivAt (fun r : ℝ => phi (x - r • θ))
      ((⟪θ, x⟫_ℝ - s * ‖θ‖ ^ 2) * phi (x - s • θ)) s := by
  have he : (fun r : ℝ => phi (x - r • θ)) =
      (fun r : ℝ => phi x * exp (r * ⟪θ, x⟫_ℝ - r ^ 2 * ‖θ‖ ^ 2 / 2)) := by
    funext r
    rw [← phi_mul_kernel_mean_scaling, kernel, real_inner_smul_right]
  rw [he]
  convert! (((hasDerivAt_id s).mul_const ⟪θ, x⟫_ℝ).sub
    ((((hasDerivAt_id s).pow 2).mul_const (‖θ‖ ^ 2)).div_const 2)).exp.const_mul
      (phi x) using 1
  rw [← phi_mul_kernel_mean_scaling]
  dsimp [kernel]
  rw [real_inner_smul_right]
  ring

/-- Differentiate the genuine mixture integral using the existing compact-prior
dominated-differentiation theorem. This is a pointwise density derivative,
not yet a derivative of its KL or Hellinger integral over Euclidean space. -/
theorem meanScaledDensity_hasDerivAt {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (s : ℝ) :
    HasDerivAt (fun r : ℝ => meanScaledDensity μ r x)
      (∫ θ : Ball d M, (⟪θ.val, x⟫_ℝ - s * ‖θ.val‖ ^ 2) *
        phi (x - s • θ.val) ∂μ) s := by
  refine hasDerivAt_integral_compact_prior μ
    (F := fun r θ => phi (x - r • θ.val))
    (F' := fun r θ => (⟪θ.val, x⟫_ℝ - r * ‖θ.val‖ ^ 2) * phi (x - r • θ.val))
    ?_ ?_ ?_ s
  · unfold Function.uncurry phi
    fun_prop
  · unfold Function.uncurry phi
    fun_prop
  · exact fun r θ => phi_mean_scaling_hasDerivAt θ.val x r

@[simp] theorem meanScaledDensity_zero {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    meanScaledDensity μ 0 = phi := by
  funext x
  simp [meanScaledDensity]

@[simp] theorem meanScaledDensity_one {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) : meanScaledDensity μ 1 = mixtureDensity μ := by
  funext x
  simp [meanScaledDensity, mixtureDensity]

theorem meanScaledDensity_pos {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) (x : Space d) :
    0 < meanScaledDensity μ s x := by
  rw [meanScaledDensity_eq_partition]
  exact mul_pos (phi_pos x) (partition_pos hM μ (s • x) (s ^ 2))

theorem continuous_meanScaledDensity {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    Continuous (fun p : Space d × ℝ => meanScaledDensity μ p.2 p.1) := by
  simp_rw [meanScaledDensity_eq_partition]
  have hc : Continuous (fun p : Space d × ℝ => (p.2 • p.1, p.2 ^ 2)) :=
    (continuous_snd.smul continuous_fst).prodMk (continuous_snd.pow 2)
  exact ((continuous_phi d).comp continuous_fst).mul
    (Continuous.comp (g := fun q : Space d × ℝ => partition μ q.1 q.2)
      (f := fun p : Space d × ℝ => (p.2 • p.1, p.2 ^ 2)) (continuous_partition μ) hc)

theorem continuous_meanScaledPosterior {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    Continuous (fun p : Space d × ℝ => meanScaledPosterior μ p.2 p.1) := by
  change Continuous (fun p : Space d × ℝ => posteriorMean μ (p.2 • p.1) (p.2 ^ 2))
  have hc : Continuous (fun p : Space d × ℝ => (p.2 • p.1, p.2 ^ 2)) :=
    (continuous_snd.smul continuous_fst).prodMk (continuous_snd.pow 2)
  exact Continuous.comp (g := fun q : Space d × ℝ => posteriorMean μ q.1 q.2)
    (f := fun p : Space d × ℝ => (p.2 • p.1, p.2 ^ 2)) (continuous_posteriorMean hM μ) hc

theorem continuous_meanScaledGap {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Continuous (fun p : Space d × ℝ => meanScaledGap μ ν p.2 p.1) := by
  exact (continuous_meanScaledPosterior hM μ).sub (continuous_meanScaledPosterior hM ν)

theorem continuous_meanScaledDensity_space {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (s : ℝ) :
    Continuous (meanScaledDensity μ s) := by
  exact Continuous.comp (g := fun p : Space d × ℝ => meanScaledDensity μ p.2 p.1)
    (f := fun x : Space d => (x, s)) (continuous_meanScaledDensity μ)
    (continuous_id.prodMk continuous_const)

theorem continuous_meanScaledGap_space {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) : Continuous (meanScaledGap μ ν s) := by
  exact Continuous.comp (g := fun p : Space d × ℝ => meanScaledGap μ ν p.2 p.1)
    (f := fun x : Space d => (x, s)) (continuous_meanScaledGap hM μ ν)
    (continuous_id.prodMk continuous_const)

theorem norm_meanScaledPosterior_le {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) (x : Space d) :
    ‖meanScaledPosterior μ s x‖ ≤ M :=
  norm_posteriorMean_le hM μ (s • x) (s ^ 2)

theorem norm_meanScaledGap_le {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (x : Space d) : ‖meanScaledGap μ ν s x‖ ≤ 2 * M := by
  have h := norm_sub_le (meanScaledPosterior μ s x) (meanScaledPosterior ν s x)
  have hμ := norm_meanScaledPosterior_le hM μ s x
  have hν := norm_meanScaledPosterior_le hM ν s x
  dsimp [meanScaledGap]
  linarith

theorem sq_norm_meanScaledGap_le {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (x : Space d) : ‖meanScaledGap μ ν s x‖ ^ 2 ≤ 4 * M ^ 2 := by
  have h := norm_meanScaledGap_le hM μ ν s x
  nlinarith [norm_nonneg (meanScaledGap μ ν s x)]

/-- The common Gaussian factor cancels from the log-likelihood ratio. -/
theorem log_meanScaledDensity_ratio {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (x : Space d) :
    log (meanScaledDensity μ s x / meanScaledDensity ν s x) =
      log (partition μ (s • x) (s ^ 2)) - log (partition ν (s • x) (s ^ 2)) := by
  rw [Real.log_div (meanScaledDensity_pos hM μ s x).ne'
    (meanScaledDensity_pos hM ν s x).ne', meanScaledDensity_eq_partition,
    meanScaledDensity_eq_partition,
    Real.log_mul (phi_pos x).ne' (partition_pos hM μ (s • x) (s ^ 2)).ne',
    Real.log_mul (phi_pos x).ne' (partition_pos hM ν (s • x) (s ^ 2)).ne']
  ring

/-- The central Gaussian score identity in the elementary proof, obtained by
reusing the already proved gradient of the actual log partition. -/
theorem log_meanScaledDensity_ratio_hasGradientAt {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (x : Space d) :
    HasGradientAt (fun y => log (meanScaledDensity μ s y / meanScaledDensity ν s y))
      (s • meanScaledGap μ ν s x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hμ := (log_partition_hasGradientAt hM μ (s • x) (s ^ 2)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul s)
  have hν := (log_partition_hasGradientAt hM ν (s • x) (s ^ 2)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul s)
  convert! hμ.sub hν using 1
  · funext y
    exact log_meanScaledDensity_ratio hM μ ν s y
  · ext y
    simp [meanScaledGap, meanScaledPosterior, InnerProductSpace.toDual_apply_apply, mul_sub]

theorem gradient_log_meanScaledDensity_ratio {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (x : Space d) :
    gradient (fun y => log (meanScaledDensity μ s y / meanScaledDensity ν s y)) x =
      s • meanScaledGap μ ν s x :=
  (log_meanScaledDensity_ratio_hasGradientAt hM μ ν s x).gradient

/-- Map a compact-prior point to a scaled point in the same ball. -/
def priorScalingMap {d : ℕ} {M : ℝ} (s : ℝ) (hs : |s| ≤ 1) :
    Ball d M → Ball d M := fun θ => ⟨s • θ.val, by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |s| * ‖θ.val‖ ≤ 1 * ‖θ.val‖ :=
          mul_le_mul_of_nonneg_right hs (norm_nonneg _)
        _ = ‖θ.val‖ := one_mul _
        _ ≤ M := θ.property⟩

theorem continuous_priorScalingMap {d : ℕ} {M : ℝ} (s : ℝ) (hs : |s| ≤ 1) :
    Continuous (priorScalingMap (d := d) (M := M) s hs) := by
  unfold priorScalingMap
  fun_prop

def meanScaledPrior {d : ℕ} {M : ℝ} (μ : Measure (Ball d M))
    (s : ℝ) (hs : |s| ≤ 1) : Measure (Ball d M) :=
  μ.map (priorScalingMap s hs)

instance meanScaledPrior_isProbabilityMeasure {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) (hs : |s| ≤ 1) :
    IsProbabilityMeasure (meanScaledPrior μ s hs) :=
  Measure.isProbabilityMeasure_map (continuous_priorScalingMap s hs).measurable.aemeasurable

/-- This bridge lets the existing finiteness theorem apply to the interpolation. -/
theorem meanScaledDensity_eq_mixtureDensity {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) (s : ℝ) (hs : |s| ≤ 1) :
    meanScaledDensity μ s = mixtureDensity (meanScaledPrior μ s hs) := by
  funext x
  have hc : Continuous (fun θ : Ball d M => phi (x - θ.val)) :=
    (continuous_phi d).comp (continuous_const.sub continuous_subtype_val)
  rw [mixtureDensity, meanScaledPrior,
    integral_map (continuous_priorScalingMap s hs).measurable.aemeasurable
      hc.aestronglyMeasurable]
  rfl

theorem integral_meanScaledDensity {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) (hs : |s| ≤ 1) :
    (∫ x, meanScaledDensity μ s x) = 1 := by
  rw [meanScaledDensity_eq_mixtureDensity μ s hs]
  exact integral_mixtureDensity _

theorem integrable_meanScaledDensity {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) (hs : |s| ≤ 1) :
    Integrable (meanScaledDensity μ s) := by
  rw [meanScaledDensity_eq_mixtureDensity μ s hs]
  exact integrable_mixtureDensity _

theorem finiteDivergences_meanScaled {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (hs : |s| ≤ 1) :
    FiniteDivergences volume (meanScaledDensity μ s) (meanScaledDensity ν s) := by
  rw [meanScaledDensity_eq_mixtureDensity μ s hs,
    meanScaledDensity_eq_mixtureDensity ν s hs]
  exact finiteDivergences_mixture hM _ _

def meanScalingJeffreys {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  kl volume (meanScaledDensity μ s) (meanScaledDensity ν s) +
    kl volume (meanScaledDensity ν s) (meanScaledDensity μ s)

def meanScalingHellinger {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  hellingerSq volume (meanScaledDensity μ s) (meanScaledDensity ν s)

@[simp] theorem meanScalingJeffreys_zero {d : ℕ} {M : ℝ}
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    meanScalingJeffreys μ ν 0 = 0 := by simp [meanScalingJeffreys]

@[simp] theorem meanScalingHellinger_zero {d : ℕ} {M : ℝ}
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    meanScalingHellinger μ ν 0 = 0 := by simp [meanScalingHellinger]

@[simp] theorem meanScalingJeffreys_one {d : ℕ} {M : ℝ}
    (μ ν : Measure (Ball d M)) :
    meanScalingJeffreys μ ν 1 = kl volume (mixtureDensity μ) (mixtureDensity ν) +
      kl volume (mixtureDensity ν) (mixtureDensity μ) := by simp [meanScalingJeffreys]

@[simp] theorem meanScalingHellinger_one {d : ℕ} {M : ℝ}
    (μ ν : Measure (Ball d M)) :
    meanScalingHellinger μ ν 1 = hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  simp [meanScalingHellinger]

end GaussianComparison.GaussianModel
