import GaussianComparison.MeanScalingTests
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! The weak continuity equation for the actual mixture, proved by Gaussian
integration by parts and Fubini. All three products in integration by parts
are integrable; no boundary term or stochastic identity is postulated. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

theorem phi_hasFDerivAt {d : ℕ} (x : Space d) :
    HasFDerivAt phi ((-phi x) • innerSL ℝ x) x := by
  convert! (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (-1 / 2 : ℝ)).exp).const_smul
    (normalizer d) using 1
  · funext y
    simp only [phi, Pi.smul_apply, smul_eq_mul]
    congr 2; ring
  · ext v
    have he : (-1 / 2 : ℝ) * ‖x‖ ^ 2 = -‖x‖ ^ 2 / 2 := by ring
    simp only [phi, smul_apply, innerSL_apply_apply, Pi.smul_apply, smul_eq_mul, he]
    ring

theorem phi_sub_fderiv {d : ℕ} (a x v : Space d) :
    fderiv ℝ (fun y => phi (y - a)) x v = -phi (x - a) * ⟪x - a, v⟫_ℝ := by
  have h := (phi_hasFDerivAt (x - a)).comp x ((hasFDerivAt_id x).sub_const a)
  change HasFDerivAt (fun y => phi (y - a)) _ x at h
  rw [h.fderiv]
  simp [innerSL_apply_apply, inner_sub_left]

theorem fixed_growth {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → Space d → E} (s : ℝ)
    (hb : ∀ T : ℝ, 0 ≤ T → ExpGrowth (fun (r : {r : ℝ // |r| ≤ T}) x => f r.val x)) :
    ExpGrowth (fun (_ : Unit) x => f s x) :=
  (hb (|s| + 1) (by positivity)).reparam (fun _ => ⟨s, by linarith⟩)

theorem integrable_scaledPartitionDot_mul {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ)
    {f : Space d → ℝ} (hf : Continuous f)
    (hb : ExpGrowth (fun (_ : Unit) x => f x)) :
    Integrable (fun x => phi x * scaledPartitionDot μ s x * f x) := by
  have hdot := fixed_growth s (fun T hT => scaledPartitionDot_growth hM hT μ)
  have hc : Continuous (scaledPartitionDot μ s) :=
    (continuous_scaledPartitionDot μ).comp (continuous_const.prodMk continuous_id)
  convert! (hdot.mul hb).gaussian_integrable () (hc.mul hf).aestronglyMeasurable using 1
  funext x; ring

theorem integrable_meanScaledDensity_mul_inner {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ)
    {G : Space d → Space d} (hG : Continuous G)
    (hb : ExpGrowth (fun (_ : Unit) x => G x)) :
    Integrable (fun x => meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ) := by
  have hz := fixed_growth s (fun T hT => scaledPartition_growth hM hT μ)
  have hu := fixed_growth s (fun T hT => meanScaledPosterior_growth hM μ hT)
  have hc : Continuous (scaledPartition μ s) :=
    Continuous.comp (g := Function.uncurry (scaledPartition μ))
      (f := fun x : Space d => (s, x)) (continuous_scaledPartition μ)
      (continuous_const.prodMk continuous_id)
  have huc : Continuous (meanScaledPosterior μ s) :=
    Continuous.comp (g := fun p : Space d × ℝ => meanScaledPosterior μ p.2 p.1)
      (f := fun x : Space d => (x, s)) (continuous_meanScaledPosterior hM μ)
      (continuous_id.prodMk continuous_const)
  have hprod : Integrable (fun x => phi x * (scaledPartition μ s x *
      ⟪meanScaledPosterior μ s x, G x⟫_ℝ)) :=
    (hz.mul (hu.inner hb)).gaussian_integrable () (hc.mul (huc.inner hG)).aestronglyMeasurable
  apply hprod.congr
  filter_upwards [] with x
  rw [meanScaledDensity_eq_partition]
  dsimp [scaledPartition]; ring

theorem meanScaledDensity_smul_posterior {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) (x : Space d) :
    meanScaledDensity μ s x • meanScaledPosterior μ s x =
      ∫ θ, phi (x - s • θ.val) • θ.val ∂μ := by
  rw [meanScaledDensity_eq_partition, meanScaledPosterior, posteriorMean, smul_smul]
  rw [mul_assoc, mul_inv_cancel₀ (partition_pos hM μ _ _).ne', mul_one, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [smul_smul, phi_mul_kernel_mean_scaling]

theorem meanScaledDensity_mul_inner_posterior {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) (x v : Space d) :
    meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, v⟫_ℝ =
      ∫ θ, phi (x - s • θ.val) * ⟪θ.val, v⟫_ℝ ∂μ := by
  have hi : Integrable (fun θ : Ball d M => phi (x - s • θ.val) • θ.val) μ := by
    have hc : Continuous (fun θ : Ball d M => phi (x - s • θ.val) • θ.val) := by
      unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have he := (innerSL ℝ v).integral_comp_comm hi
  simp only [innerSL_apply_apply, real_inner_smul_right] at he
  calc
    _ = ⟪v, meanScaledDensity μ s x • meanScaledPosterior μ s x⟫_ℝ := by
      rw [real_inner_smul_right, real_inner_comm v]
    _ = ⟪v, ∫ θ, phi (x - s • θ.val) • θ.val ∂μ⟫_ℝ := by
      rw [meanScaledDensity_smul_posterior hM μ s x]
    _ = ∫ θ, phi (x - s • θ.val) * ⟪v, θ.val⟫_ℝ ∂μ := he.symm
    _ = _ := by
      apply integral_congr_ae; filter_upwards [] with θ; rw [real_inner_comm v]

/-- The continuity equation tested against a function of at most exponential
growth. This is the elementary substitute for the stochastic evolution step. -/
theorem meanScaling_weak_derivative {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ)
    (f : Space d → ℝ) (G : Space d → Space d)
    (hf : Continuous f) (hG : Continuous G)
    (hd : ∀ x, HasGradientAt f (G x) x)
    (hfb : ExpGrowth (fun (_ : Unit) x => f x))
    (hGb : ExpGrowth (fun (_ : Unit) x => G x)) :
    (∫ x, phi x * scaledPartitionDot μ s x * f x) =
      ∫ x, meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ := by
  let T := |s| + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let r : {r : ℝ // |r| ≤ T} := ⟨s, by dsimp [T]; linarith⟩
  let K := fun (θ : Ball d M) (x : Space d) => kernel θ.val (s • x) (s ^ 2)
  let W := fun (θ : Ball d M) (x : Space d) => ⟪θ.val, x⟫_ℝ - s * ‖θ.val‖ ^ 2
  have hK : ExpGrowth K := (scaledKernel_growth hM hT).reparam (fun θ => (r, θ))
  have hW : ExpGrowth W := (scaledWeight_growth hM hT).reparam (fun θ => (r, θ))
  have hθ : ExpGrowth (fun (θ : Ball d M) (_ : Space d) => θ.val) :=
    ExpGrowth.of_bounded M hM (fun θ _ => θ.property)
  have hF := hfb.reparam (fun (_ : Ball d M) => ())
  have hGrad := hGb.reparam (fun (_ : Ball d M) => ())
  have hI := hθ.inner hGrad
  have hb₁ := (hK.mul hW).mul hF
  have hb₂ := hK.mul hI
  have hb₀ := hK.mul hF
  have hc₁ : Continuous (fun p : Space d × Ball d M => K p.2 p.1 * W p.2 p.1 * f p.1) := by
    exact (by unfold K W kernel; fun_prop : Continuous (fun p : Space d × Ball d M =>
      K p.2 p.1 * W p.2 p.1)).mul
        (hf.comp continuous_fst)
  have hc₂ : Continuous (fun p : Space d × Ball d M => K p.2 p.1 * ⟪p.2.val, G p.1⟫_ℝ) := by
    exact (by unfold K kernel; fun_prop : Continuous (fun p : Space d × Ball d M => K p.2 p.1)).mul
      (continuous_subtype_val.comp continuous_snd |>.inner (hG.comp continuous_fst))
  have hp₁ := hb₁.gaussian_integrable_prod (μ := μ) hc₁.aestronglyMeasurable
  have hp₂ := hb₂.gaussian_integrable_prod (μ := μ) hc₂.aestronglyMeasurable
  have hi₁ (θ : Ball d M) : Integrable (fun x => W θ x * phi (x - s • θ.val) * f x) := by
    convert! hb₁.gaussian_integrable θ
      (hc₁.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable using 1
    funext x; rw [← phi_mul_kernel_mean_scaling]; dsimp [K]; ring
  have hi₂ (θ : Ball d M) : Integrable (fun x => phi (x - s • θ.val) * ⟪G x, θ.val⟫_ℝ) := by
    convert! hb₂.gaussian_integrable θ
      (hc₂.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable using 1
    funext x; rw [← phi_mul_kernel_mean_scaling]; dsimp [K]; rw [real_inner_comm]; ring
  have hi₀ (θ : Ball d M) : Integrable (fun x => phi (x - s • θ.val) * f x) := by
    have hc : Continuous (fun x => K θ x * f x) :=
      (by unfold K kernel; fun_prop : Continuous (K θ)).mul hf
    convert! hb₀.gaussian_integrable θ hc.aestronglyMeasurable using 1
    funext x; rw [← phi_mul_kernel_mean_scaling]; dsimp [K]; ring
  have hparts (θ : Ball d M) :
      (∫ x, W θ x * phi (x - s • θ.val) * f x) =
        ∫ x, phi (x - s • θ.val) * ⟪θ.val, G x⟫_ℝ := by
    have hpd (x : Space d) : fderiv ℝ (fun y => phi (y - s • θ.val)) x θ.val =
        -(W θ x * phi (x - s • θ.val)) := by
      rw [phi_sub_fderiv]
      dsimp [W]
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        real_inner_comm x θ.val]
      ring
    have h₁ : Integrable (fun x => fderiv ℝ (fun y => phi (y - s • θ.val)) x θ.val * f x) := by
      simp_rw [hpd]
      convert! (hi₁ θ).const_mul (-1) using 1
      funext x; ring
    have h₂ : Integrable (fun x => phi (x - s • θ.val) * fderiv ℝ f x θ.val) := by
      simp_rw [(hd _).fderiv_apply]
      exact hi₂ θ
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ (hi₀ θ)
      (fun x _ => ((phi_hasFDerivAt _).comp x ((hasFDerivAt_id x).sub_const _)).differentiableAt)
      (fun x _ => (hd x).differentiableAt)
    simp_rw [hpd, (hd _).fderiv_apply, neg_mul, integral_neg, neg_neg] at he
    convert! he.symm using 1
    congr 1; funext x; rw [real_inner_comm]
  calc
    (∫ x, phi x * scaledPartitionDot μ s x * f x) =
        ∫ x, ∫ θ, phi x * (K θ x * W θ x * f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      have heq : (∫ θ, K θ x * W θ x * f x ∂μ) =
          (∫ θ, W θ x * K θ x ∂μ) * f x := by
        rw [← integral_mul_const]
        apply integral_congr_ae; filter_upwards [] with θ; ring
      rw [integral_const_mul, heq]
      dsimp [scaledPartitionDot, K, W]; ring
    _ = ∫ θ, (∫ x : Space d, phi x * (K θ x * W θ x * f x)) ∂μ := integral_integral_swap hp₁
    _ = ∫ θ, (∫ x : Space d, phi x * (K θ x * ⟪θ.val, G x⟫_ℝ)) ∂μ := by
      apply integral_congr_ae; filter_upwards [] with θ
      convert! hparts θ using 1 <;>
        (congr 1; funext x; rw [← phi_mul_kernel_mean_scaling]; dsimp [K]; ring)
    _ = ∫ x, ∫ θ, phi x * (K θ x * ⟪θ.val, G x⟫_ℝ) ∂μ := (integral_integral_swap hp₂).symm
    _ = _ := by
      apply integral_congr_ae; filter_upwards [] with x
      rw [meanScaledDensity_mul_inner_posterior hM μ s x (G x)]
      apply integral_congr_ae; filter_upwards [] with θ
      rw [← phi_mul_kernel_mean_scaling]; dsimp [K]; ring

end GaussianComparison.GaussianModel
