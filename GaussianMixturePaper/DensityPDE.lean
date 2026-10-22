import GaussianMixturePaper.DensityRegularity
import GaussianMixturePaper.DeBruijn
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Module

/-! Equation (3.2), with divergence and Laplacian defined using actual coordinate
derivatives. The proof differentiates the compact-prior integral twice. -/

noncomputable section
open MeasureTheory Real Set Filter
open scoped InnerProductSpace ContDiff Topology
open GaussianComparison GaussianComparison.GaussianModel

namespace GaussianMixturePaper

variable {d : ℕ} {M : ℝ}

/-- Coordinate divergence of a vector field in the standard orthonormal basis. -/
def coordinateDivergence (F : Space d → Space d) (x : Space d) : ℝ :=
  ∑ i : Fin d, deriv (fun s : ℝ =>
    ⟪F (x + s • EuclideanSpace.basisFun (Fin d) ℝ i),
      EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ) 0

theorem phi_line_hasDerivAt (a x v : Space d) (s : ℝ) :
    HasDerivAt (fun u : ℝ => phi (x + u • v - a))
      (-⟪x + s • v - a, v⟫_ℝ * phi (x + s • v - a)) s := by
  have hl := (((hasDerivAt_id s).smul_const v).const_add x).sub_const a
  convert! (phi_hasFDerivAt (x + s • v - a)).comp_hasDerivAt s hl using 1
  simp [innerSL_apply_apply, smul_apply, inner_add_left, inner_sub_left, real_inner_smul_left]
  ring

theorem phi_line_derivative_hasDerivAt (a x v : Space d) (s : ℝ) :
    HasDerivAt (fun u : ℝ => -⟪x + u • v - a, v⟫_ℝ * phi (x + u • v - a))
      ((⟪x + s • v - a, v⟫_ℝ ^ 2 - ‖v‖ ^ 2) * phi (x + s • v - a)) s := by
  have hi : HasDerivAt (fun u : ℝ => -⟪x + u • v - a, v⟫_ℝ) (-‖v‖ ^ 2) s := by
    convert! (((hasDerivAt_id s).mul_const (‖v‖ ^ 2)).const_add ⟪x - a, v⟫_ℝ).neg using 1
    · funext u
      simp [inner_add_left, inner_sub_left, real_inner_smul_left]
      ring
    · simp
  convert! hi.mul (phi_line_hasDerivAt a x v s) using 1
  ring

theorem density_line_hasDerivAt (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    (t : ℝ) (x v : Space d) (s : ℝ) :
    HasDerivAt (fun u : ℝ => meanScaledDensity μ t (x + u • v))
      (∫ θ : Ball d M, -⟪x + s • v - t • θ.val, v⟫_ℝ *
        phi (x + s • v - t • θ.val) ∂μ) s := by
  exact hasDerivAt_integral_compact_prior μ
    (F := fun u θ => phi (x + u • v - t • θ.val))
    (F' := fun u θ => -⟪x + u • v - t • θ.val, v⟫_ℝ * phi (x + u • v - t • θ.val))
    (by unfold Function.uncurry phi; fun_prop)
    (by unfold Function.uncurry phi; fun_prop)
    (fun u θ => phi_line_hasDerivAt (t • θ.val) x v u) s

theorem density_line_second_derivative (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    (t : ℝ) (x v : Space d) (s : ℝ) :
    deriv (deriv (fun u : ℝ => meanScaledDensity μ t (x + u • v))) s =
      ∫ θ : Ball d M, (⟪x + s • v - t • θ.val, v⟫_ℝ ^ 2 - ‖v‖ ^ 2) *
        phi (x + s • v - t • θ.val) ∂μ := by
  have hfirst : deriv (fun u : ℝ => meanScaledDensity μ t (x + u • v)) =
      fun u => ∫ θ : Ball d M, -⟪x + u • v - t • θ.val, v⟫_ℝ *
        phi (x + u • v - t • θ.val) ∂μ := by
    funext u
    exact (density_line_hasDerivAt μ t x v u).deriv
  rw [hfirst]
  exact (hasDerivAt_integral_compact_prior μ
    (F := fun u θ => -⟪x + u • v - t • θ.val, v⟫_ℝ * phi (x + u • v - t • θ.val))
    (F' := fun u θ => (⟪x + u • v - t • θ.val, v⟫_ℝ ^ 2 - ‖v‖ ^ 2) *
      phi (x + u • v - t • θ.val))
    (by unfold Function.uncurry phi; fun_prop)
    (by unfold Function.uncurry phi; fun_prop)
    (fun u θ => phi_line_derivative_hasDerivAt (t • θ.val) x v u) s).deriv

/-- The ordinary Euclidean Laplacian of the actual mixture density. -/
theorem density_coordinateLaplacian (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    (t : ℝ) (x : Space d) :
    coordinateLaplacian (meanScaledDensity μ t) x =
      ∫ θ : Ball d M, (‖x - t • θ.val‖ ^ 2 - d) * phi (x - t • θ.val) ∂μ := by
  unfold coordinateLaplacian
  simp_rw [density_line_second_derivative, zero_smul, add_zero]
  have hi (i : Fin d) : Integrable (fun θ : Ball d M =>
      (⟪x - t • θ.val, EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ ^ 2 -
        ‖EuclideanSpace.basisFun (Fin d) ℝ i‖ ^ 2) * phi (x - t • θ.val)) μ := by
    have hc : Continuous (fun θ : Ball d M =>
      (⟪x - t • θ.val, EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ ^ 2 -
        ‖EuclideanSpace.basisFun (Fin d) ℝ i‖ ^ 2) * phi (x - t • θ.val)) := by
      unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [← Finset.sum_mul, Finset.sum_sub_distrib,
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_sq_inner_left]
  simp

theorem density_radial_component_derivative (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    (t : ℝ) (x v : Space d) :
    deriv (fun s : ℝ => ⟪meanScaledDensity μ t (x + s • v) • (x + s • v), v⟫_ℝ) 0 =
      ∫ θ : Ball d M, (‖v‖ ^ 2 - ⟪x, v⟫_ℝ * ⟪x - t • θ.val, v⟫_ℝ) *
        phi (x - t • θ.val) ∂μ := by
  have hc : HasDerivAt (fun s : ℝ => ⟪x + s • v, v⟫_ℝ) (‖v‖ ^ 2) 0 := by
    convert! ((hasDerivAt_id 0).mul_const (‖v‖ ^ 2)).const_add ⟪x, v⟫_ℝ using 1
    · funext s
      simp [inner_add_left, real_inner_smul_left]
    · simp
  have hd := (density_line_hasDerivAt μ t x v 0).mul hc
  simp only [zero_smul, add_zero] at hd
  change HasDerivAt (fun s : ℝ => meanScaledDensity μ t (x + s • v) * ⟪x + s • v, v⟫_ℝ) _ 0 at hd
  simp only [real_inner_smul_left]
  rw [hd.deriv]
  have hi : Integrable (fun θ : Ball d M => -⟪x - t • θ.val, v⟫_ℝ * phi (x - t • θ.val)) μ := by
    have hc : Continuous (fun θ : Ball d M => -⟪x - t • θ.val, v⟫_ℝ * phi (x - t • θ.val)) := by
      unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have hj : Integrable (fun θ : Ball d M => phi (x - t • θ.val)) μ := by
    have hc : Continuous (fun θ : Ball d M => phi (x - t • θ.val)) := by unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [← integral_mul_const, meanScaledDensity, ← integral_mul_const,
    ← integral_add (hi.mul_const _) (hj.mul_const _)]
  apply integral_congr_ae
  filter_upwards [] with θ
  ring

/-- The coordinate divergence of the radial density field. -/
theorem density_coordinateDivergence (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    (t : ℝ) (x : Space d) :
    coordinateDivergence (fun y => meanScaledDensity μ t y • y) x =
      ∫ θ : Ball d M, ((d : ℝ) - ⟪x, x - t • θ.val⟫_ℝ) * phi (x - t • θ.val) ∂μ := by
  unfold coordinateDivergence
  simp_rw [density_radial_component_derivative]
  have hi (i : Fin d) : Integrable (fun θ : Ball d M =>
      (‖EuclideanSpace.basisFun (Fin d) ℝ i‖ ^ 2 -
        ⟪x, EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ *
        ⟪x - t • θ.val, EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ) * phi (x - t • θ.val)) μ := by
    have hc : Continuous (fun θ : Ball d M =>
      (‖EuclideanSpace.basisFun (Fin d) ℝ i‖ ^ 2 -
        ⟪x, EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ *
        ⟪x - t • θ.val, EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ) * phi (x - t • θ.val)) := by
      unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  have hb := (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner x (x - t • θ.val)
  simp_rw [real_inner_comm (x - t • θ.val)] at hb
  rw [real_inner_comm x (x - t • θ.val)] at hb
  rw [hb]
  simp

/-- The exact density PDE (3.2), including the parameter value t = 0. -/
theorem density_PDE (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (t : ℝ) (x : Space d) :
    t * deriv (fun s => meanScaledDensity μ s x) t =
      -coordinateDivergence (fun y => meanScaledDensity μ t y • y) x -
        coordinateLaplacian (meanScaledDensity μ t) x := by
  rw [density_deriv_time, density_coordinateDivergence, density_coordinateLaplacian]
  have hi : Integrable (fun θ : Ball d M => ((d : ℝ) - ⟪x, x - t • θ.val⟫_ℝ) *
      phi (x - t • θ.val)) μ := by
    have hc : Continuous (fun θ : Ball d M => ((d : ℝ) - ⟪x, x - t • θ.val⟫_ℝ) *
      phi (x - t • θ.val)) := by unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have hj : Integrable (fun θ : Ball d M => (‖x - t • θ.val‖ ^ 2 - (d : ℝ)) *
      phi (x - t • θ.val)) μ := by
    have hc : Continuous (fun θ : Ball d M => (‖x - t • θ.val‖ ^ 2 - (d : ℝ)) *
      phi (x - t • θ.val)) := by unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [← integral_const_mul, ← integral_neg]
  have hsub := integral_sub hi.neg hj
  simp only [Pi.neg_apply] at hsub
  rw [← hsub]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm θ.val x]
  ring

/-- Gaussian damping dominates every exponential spatial envelope. -/
theorem gaussian_expGrowth_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space d → E} (hf : ExpGrowth (fun (_ : Unit) x => f x)) :
    Tendsto (fun x => phi x • f x) (cocompact (Space d)) (𝓝 0) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf
  have hn : Tendsto (fun x : Space d => ‖x‖ ^ 2) (cocompact (Space d)) atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp tendsto_norm_cocompact_atTop
  have hq : Tendsto (fun x : Space d => ‖x‖ ^ 2 / 4) (cocompact (Space d)) atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using hn.const_mul_atTop (by norm_num : (0 : ℝ) < 4⁻¹)
  have hz : Tendsto (fun x : Space d => normalizer d * C * exp (c ^ 2) * exp (-(‖x‖ ^ 2 / 4)))
      (cocompact (Space d)) (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hq).const_mul
      (normalizer d * C * exp (c ^ 2))
  apply squeeze_zero_norm _ hz
  intro x
  rw [norm_smul, Real.norm_of_nonneg (phi_pos x).le]
  calc
    phi x * ‖f x‖ ≤ phi x * (C * exp (c * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (hb () x) (phi_pos x).le
    _ = normalizer d * C * exp (-‖x‖ ^ 2 / 2 + c * ‖x‖) := by
      rw [exp_add]; unfold phi; ring
    _ ≤ normalizer d * C * exp (c ^ 2 - ‖x‖ ^ 2 / 4) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (normalizer_pos d).le hC)
      apply exp_le_exp.mpr
      nlinarith [sq_nonneg (‖x‖ / 2 - c)]
    _ = _ := by rw [exp_sub, exp_neg]; ring

private theorem expGrowth_vector_add {f g : Space d → Space d}
    (hf : ExpGrowth (fun (_ : Unit) x => f x))
    (hg : ExpGrowth (fun (_ : Unit) x => g x)) :
    ExpGrowth (fun (_ : Unit) x => f x + g x) := by
  apply (hf.norm.add hg.norm).mono
  intro a x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    using norm_add_le (f x) (g x)

private theorem expGrowth_identity : ExpGrowth (fun (_ : Unit) (x : Space d) => x) := by
  apply (ExpGrowth.radius (A := Unit) (d := d)).mono
  intro a x
  simp

/-- The exact score formula for one mixture density. -/
theorem density_hasGradientAt_score (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) (x : Space d) :
    HasGradientAt (meanScaledDensity μ t)
      (meanScaledDensity μ t x • (t • meanScaledPosterior μ t x - x)) x := by
  have hi : Integrable (fun θ : Ball d M => phi (x - t • θ.val)) μ := by
    have hc : Continuous (fun θ : Ball d M => phi (x - t • θ.val)) := by unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have hv : Integrable (fun θ : Ball d M => phi (x - t • θ.val) • θ.val) μ := by
    have hc : Continuous (fun θ : Ball d M => phi (x - t • θ.val) • θ.val) := by unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have he : (∫ θ : Ball d M, phi (x - t • θ.val) • (x - t • θ.val) ∂μ) =
      meanScaledDensity μ t x • x - t • (meanScaledDensity μ t x • meanScaledPosterior μ t x) := by
    rw [meanScaledDensity_smul_posterior hM μ t x]
    have hp : (fun θ : Ball d M => phi (x - t • θ.val) • (x - t • θ.val)) =
        (fun θ => phi (x - t • θ.val) • x - t • (phi (x - t • θ.val) • θ.val)) := by
      funext θ
      module
    have hsub := integral_sub (hi.smul_const x) (hv.smul t)
    simp only [Pi.smul_apply] at hsub
    rw [hp, hsub, integral_smul_const, integral_smul]
    rfl
  convert! density_hasGradientAt_space μ t x using 1
  rw [he]
  module

/-- Boundary decay of the radial flux, for any generator with the indicated
proved spatial envelope. -/
theorem generator_radial_flux_decay (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (f : ℝ → ℝ)
    (hf : ExpGrowth (fun (_ : Unit) x => f (scaledRatio μ ν t x))) :
    Tendsto (fun x => (meanScaledDensity ν t x *
      f (meanScaledDensity μ t x / meanScaledDensity ν t x)) • x)
      (cocompact (Space d)) (𝓝 0) := by
  have hz := fixed_growth t (fun T hT => scaledPartition_growth hM hT ν)
  have hg : ExpGrowth (fun (_ : Unit) (x : Space d) =>
      (scaledPartition ν t x * f (scaledRatio μ ν t x)) • x) :=
    (hz.mul hf).smul (expGrowth_identity (d := d))
  have h := gaussian_expGrowth_decay hg
  convert! h using 1
  funext x
  rw [density_ratio_eq_scaledRatio μ ν, meanScaledDensity_eq_partition]
  simp only [smul_smul, scaledPartition]
  congr 1
  ring

/-- The exact gradient of the generator density, prior to the decay argument. -/
theorem generator_density_hasGradientAt (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (f : ℝ → ℝ) (hf : ∀ r, 0 < r → DifferentiableAt ℝ f r) (x : Space d) :
    HasGradientAt (fun y => meanScaledDensity ν t y *
      f (meanScaledDensity μ t y / meanScaledDensity ν t y))
      ((meanScaledDensity ν t x * f (scaledRatio μ ν t x)) •
        (t • meanScaledPosterior ν t x - x) +
       (meanScaledDensity ν t x * deriv f (scaledRatio μ ν t x) * scaledRatio μ ν t x * t) •
        meanScaledGap μ ν t x) x := by
  have hd := ((hf _ (scaledRatio_pos hM μ ν t x)).hasDerivAt).comp_hasFDerivAt x
    (scaledRatio_hasGradientAt hM μ ν t x).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (density_hasGradientAt_score hM ν t x).hasFDerivAt.mul hd using 1
  · funext y
    rw [density_ratio_eq_scaledRatio μ ν]
    rfl
  · ext v
    simp only [InnerProductSpace.toDual_apply_apply, add_apply, smul_apply, Function.comp_apply,
      inner_add_left, real_inner_smul_left, smul_eq_mul]
    ring

set_option maxHeartbeats 800000 in
/-- Decay of the full spatial gradient of q f(p/q), with both required growth
assumptions exposed for subsequent concrete discharge. -/
theorem generator_gradient_flux_decay (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (f : ℝ → ℝ) (hf : ∀ r, 0 < r → DifferentiableAt ℝ f r)
    (hfg : ExpGrowth (fun (_ : Unit) x => f (scaledRatio μ ν t x)))
    (hdfg : ExpGrowth (fun (_ : Unit) x => deriv f (scaledRatio μ ν t x))) :
    Tendsto (fun x => gradient (fun y => meanScaledDensity ν t y *
      f (meanScaledDensity μ t y / meanScaledDensity ν t y)) x)
      (cocompact (Space d)) (𝓝 0) := by
  have hz := fixed_growth t (fun T hT => scaledPartition_growth hM hT ν)
  have hu := fixed_growth t (fun T hT => meanScaledPosterior_growth hM ν hT)
  have hr := fixed_growth t (fun T hT => scaledRatio_growth hM hT μ ν)
  have hgap := fixed_growth t (fun T hT => meanScaledGap_growth hM μ ν hT)
  have htu : ExpGrowth (fun (_ : Unit) (x : Space d) => t • meanScaledPosterior ν t x) :=
    (ExpGrowth.const t).smul hu
  have hneg : ExpGrowth (fun (_ : Unit) (x : Space d) => -x) := by
    simpa only [neg_one_smul] using
      (ExpGrowth.const (-1)).smul (expGrowth_identity (d := d))
  have hscore : ExpGrowth (fun (_ : Unit) (x : Space d) => t • meanScaledPosterior ν t x - x) := by
    simpa only [sub_eq_add_neg] using expGrowth_vector_add htu hneg
  have hA : ExpGrowth (fun (_ : Unit) (x : Space d) =>
      (scaledPartition ν t x * f (scaledRatio μ ν t x)) •
        (t • meanScaledPosterior ν t x - x)) := (hz.mul hfg).smul hscore
  have hB : ExpGrowth (fun (_ : Unit) (x : Space d) =>
      (scaledPartition ν t x * deriv f (scaledRatio μ ν t x) * scaledRatio μ ν t x * t) •
        meanScaledGap μ ν t x) :=
    (((hz.mul hdfg).mul hr).mul (ExpGrowth.const t)).smul hgap
  have hg : ExpGrowth (fun (_ : Unit) (x : Space d) =>
      (scaledPartition ν t x * f (scaledRatio μ ν t x)) •
        (t • meanScaledPosterior ν t x - x) +
      (scaledPartition ν t x * deriv f (scaledRatio μ ν t x) * scaledRatio μ ν t x * t) •
        meanScaledGap μ ν t x) := expGrowth_vector_add hA hB
  have h := gaussian_expGrowth_decay hg
  convert! h using 1
  funext x
  rw [(generator_density_hasGradientAt hM μ ν t f hf x).gradient,
    meanScaledDensity_eq_partition]
  simp only [scaledPartition, smul_add, smul_smul]
  module

/-- Precisely the three generators used in Section 3. -/
def IsPaperGenerator (f : ℝ → ℝ) : Prop :=
  f = klGenerator ∨ f = hellingerGenerator ∨ f = chiSqGenerator

theorem paperGenerator_differentiable (f : ℝ → ℝ) (hf : IsPaperGenerator f)
    (r : ℝ) (hr : 0 < r) : DifferentiableAt ℝ f r := by
  rcases hf with rfl | rfl | rfl
  · exact (klGenerator_hasDerivAt hr).differentiableAt
  · exact (hellingerGenerator_hasDerivAt hr).differentiableAt
  · exact (chiSqGenerator_hasDerivAt r).differentiableAt

theorem paperGenerator_growth (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (f : ℝ → ℝ) (hf : IsPaperGenerator f) :
    ExpGrowth (fun (_ : Unit) x => f (scaledRatio μ ν t x)) := by
  have hr := fixed_growth t (fun T hT => scaledRatio_growth hM hT μ ν)
  have hl := fixed_growth t (fun T hT => scaledLogRatio_growth hM hT μ ν)
  have hs := fixed_growth t (fun T hT => scaledRootRatio_growth hM hT μ ν)
  rcases hf with rfl | rfl | rfl
  · exact ((hr.mul hl).sub hr).add (ExpGrowth.const 1)
  · simpa only [hellingerGenerator, scaledRootRatio, pow_two] using
      (hs.sub (ExpGrowth.const 1)).mul (hs.sub (ExpGrowth.const 1))
  · simpa only [chiSqGenerator, pow_two] using
      (hr.sub (ExpGrowth.const 1)).mul (hr.sub (ExpGrowth.const 1))

theorem paperGenerator_derivative_growth (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (f : ℝ → ℝ) (hf : IsPaperGenerator f) :
    ExpGrowth (fun (_ : Unit) x => deriv f (scaledRatio μ ν t x)) := by
  have hr := fixed_growth t (fun T hT => scaledRatio_growth hM hT μ ν)
  have hl := fixed_growth t (fun T hT => scaledLogRatio_growth hM hT μ ν)
  have hs := fixed_growth t (fun T hT => scaledRootRatio_growth hM hT ν μ)
  rcases hf with rfl | rfl | rfl
  · simp_rw [(klGenerator_hasDerivAt (scaledRatio_pos hM μ ν t _)).deriv]
    exact hl
  · simp_rw [(hellingerGenerator_hasDerivAt (scaledRatio_pos hM μ ν t _)).deriv]
    have he (x : Space d) : (sqrt (scaledRatio μ ν t x))⁻¹ = scaledRootRatio ν μ t x := by
      rw [← sqrt_inv]
      unfold scaledRootRatio scaledRatio
      rw [inv_div]
    simp_rw [he]
    exact (ExpGrowth.const 1).sub hs
  · simp_rw [(chiSqGenerator_hasDerivAt _).deriv]
    exact (ExpGrowth.const 2).mul (hr.sub (ExpGrowth.const 1))

/-- Both vanishing boundary conditions from Section 3, for each of its three
generators. The gradient here acts on the whole generator density q f(p/q). -/
theorem paperGenerator_boundary_conditions (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (f : ℝ → ℝ) (hf : IsPaperGenerator f) :
    Tendsto (fun x => (meanScaledDensity ν t x *
      f (meanScaledDensity μ t x / meanScaledDensity ν t x)) • x)
      (cocompact (Space d)) (𝓝 0) ∧
    Tendsto (fun x => gradient (fun y => meanScaledDensity ν t y *
      f (meanScaledDensity μ t y / meanScaledDensity ν t y)) x)
      (cocompact (Space d)) (𝓝 0) := by
  exact ⟨generator_radial_flux_decay hM μ ν t f (paperGenerator_growth hM μ ν t f hf),
    generator_gradient_flux_decay hM μ ν t f (paperGenerator_differentiable f hf)
      (paperGenerator_growth hM μ ν t f hf) (paperGenerator_derivative_growth hM μ ν t f hf)⟩

end GaussianMixturePaper
