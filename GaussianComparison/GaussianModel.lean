import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Actual compactly supported Gaussian mixtures

The prior is a probability measure on the closed Euclidean ball, and the
partition function and mixture density below are actual Bochner integrals.
This file proves the Gaussian shift identity, finiteness and positivity,
pointwise bounds, normalization with respect to Euclidean volume, and the
posterior mean bound. It does not assume a Gaussian mixture realization in a
structure. Differentiation under the integral and stochastic realization
are not claimed here.
-/

noncomputable section

open MeasureTheory Real
open scoped InnerProductSpace

namespace GaussianComparison.GaussianModel

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The actual closed Euclidean ball supporting a prior. -/
def Ball (d : ℕ) (M : ℝ) := {θ : Space d // ‖θ‖ ≤ M}

instance (d : ℕ) (M : ℝ) : MeasurableSpace (Ball d M) :=
  inferInstanceAs (MeasurableSpace {θ : Space d // ‖θ‖ ≤ M})

instance (d : ℕ) (M : ℝ) : TopologicalSpace (Ball d M) :=
  inferInstanceAs (TopologicalSpace {θ : Space d // ‖θ‖ ≤ M})

instance (d : ℕ) (M : ℝ) : BorelSpace (Ball d M) :=
  inferInstanceAs (BorelSpace {θ : Space d // ‖θ‖ ≤ M})

instance (d : ℕ) (M : ℝ) : CompactSpace (Ball d M) := by
  have hc : IsCompact {θ : Space d | ‖θ‖ ≤ M} := by
    simpa [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : Space d) M
  exact isCompact_iff_compactSpace.mp hc

/-- Exponential kernel in the manuscript. -/
def kernel {d : ℕ} (θ x : Space d) (t : ℝ) : ℝ :=
  exp (⟪θ, x⟫_ℝ - t * ‖θ‖ ^ 2 / 2)

/-- The Gaussian normalizing constant, `(2*pi)^(-d/2)`. -/
def normalizer (d : ℕ) : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2)

/-- Standard isotropic Gaussian density. -/
def phi {d : ℕ} (x : Space d) : ℝ :=
  normalizer d * exp (-‖x‖ ^ 2 / 2)

/-- Actual partition function of a compactly supported prior. -/
def partition {d : ℕ} {M : ℝ} (μ : Measure (Ball d M))
    (x : Space d) (t : ℝ) : ℝ :=
  ∫ θ, kernel θ.val x t ∂μ

/-- Actual Gaussian convolution density of a compactly supported prior. -/
def mixtureDensity {d : ℕ} {M : ℝ} (μ : Measure (Ball d M))
    (x : Space d) : ℝ :=
  ∫ θ, phi (x - θ.val) ∂μ

/-- The probability law with the proved Gaussian mixture density. -/
def mixtureMeasure {d : ℕ} {M : ℝ} (μ : Measure (Ball d M)) : Measure (Space d) :=
  volume.withDensity (fun x => ENNReal.ofReal (mixtureDensity μ x))

/-- The posterior weighted mean, before identifying it with `∇ log Z`. -/
def posteriorMean {d : ℕ} {M : ℝ} (μ : Measure (Ball d M))
    (x : Space d) (t : ℝ) : Space d :=
  (partition μ x t)⁻¹ • ∫ θ, kernel θ.val x t • θ.val ∂μ

theorem kernel_pos {d : ℕ} (θ x : Space d) (t : ℝ) :
    0 < kernel θ x t := Real.exp_pos _

theorem normalizer_pos (d : ℕ) : 0 < normalizer d := by
  unfold normalizer
  positivity

theorem phi_pos {d : ℕ} (x : Space d) : 0 < phi x :=
  mul_pos (normalizer_pos d) (Real.exp_pos _)

/-- The standard Gaussian density integrates to one against Euclidean volume. -/
theorem integral_phi (d : ℕ) : ∫ x : Space d, phi x = 1 := by
  have hg : (∫ x : Space d, exp (-‖x‖ ^ 2 / 2)) =
      (2 * Real.pi) ^ ((d : ℝ) / 2) := by
    convert GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Space d) (b := (1 / 2 : ℝ))
      (by norm_num) using 1
    · congr 1
      ext x
      congr 1
      ring
    · simp [Space, div_eq_mul_inv, mul_comm]
  simp only [phi, integral_const_mul, normalizer, hg]
  rw [← Real.rpow_add (by positivity : 0 < 2 * Real.pi)]
  have h : -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 := by ring
  rw [h, Real.rpow_zero]

theorem integrable_phi (d : ℕ) : Integrable (fun x : Space d => phi x) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_phi]
  norm_num

/-- Gaussian envelopes used for divergence integrability. -/
theorem integrable_exp_neg_mul_norm_sq (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Space d => exp (-b * ‖x‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  exact (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _).ne'

/-- Every exponential linear in the radius has finite Gaussian expectation. -/
theorem integrable_phi_mul_exp_norm (d : ℕ) (c : ℝ) :
    Integrable (fun x : Space d => phi x * exp (c * ‖x‖)) := by
  have hc : Continuous (fun x : Space d => phi x * exp (c * ‖x‖)) := by
    unfold phi
    fun_prop
  apply ((integrable_exp_neg_mul_norm_sq d (b := (1 / 4 : ℝ)) (by norm_num)).const_mul
    (normalizer d * exp (c ^ 2))).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (phi_pos x) (Real.exp_pos _))]
  calc
    phi x * exp (c * ‖x‖) =
        normalizer d * exp (-‖x‖ ^ 2 / 2 + c * ‖x‖) := by
      rw [phi, mul_assoc, ← Real.exp_add]
    _ ≤ normalizer d * exp (c ^ 2 - (1 / 4 : ℝ) * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (normalizer_pos d).le
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖x‖ / 2 - c)]
    _ = normalizer d * exp (c ^ 2) * exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) := by
      have he : c ^ 2 - (1 / 4 : ℝ) * ‖x‖ ^ 2 =
          c ^ 2 + (-(1 / 4 : ℝ) * ‖x‖ ^ 2) := by ring
      rw [he, Real.exp_add]
      ring

theorem integral_phi_sub {d : ℕ} (θ : Space d) :
    (∫ x : Space d, phi (x - θ)) = 1 := by
  rw [integral_sub_right_eq_self, integral_phi]

theorem integrable_phi_sub {d : ℕ} (θ : Space d) :
    Integrable (fun x : Space d => phi (x - θ)) :=
  (integrable_phi d).comp_sub_right θ

/-- Absolute integrability justifies Fubini for the actual mixture. -/
theorem integrable_mixture_kernel {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    Integrable (fun p : Space d × Ball d M => phi (p.1 - p.2.val))
      (volume.prod μ) := by
  have hc : Continuous (fun p : Space d × Ball d M => phi (p.1 - p.2.val)) := by
    unfold phi
    fun_prop
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun θ => integrable_phi_sub θ.val
  · have heq : (fun θ : Ball d M => ∫ x : Space d, ‖phi (x - θ.val)‖) =
        (fun _ : Ball d M => (1 : ℝ)) := by
      funext θ
      simp_rw [Real.norm_eq_abs, abs_of_pos (phi_pos _)]
      exact integral_phi_sub θ.val
    rw [heq]
    exact integrable_const 1

/-- Gaussian mixture normalization is proved, rather than assumed. -/
theorem integral_mixtureDensity {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    (∫ x : Space d, mixtureDensity μ x) = 1 := by
  unfold mixtureDensity
  rw [integral_integral_swap (integrable_mixture_kernel μ)]
  simp_rw [integral_phi_sub]
  simp

theorem integrable_mixtureDensity {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    Integrable (mixtureDensity μ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_mixtureDensity]
  norm_num

theorem mixtureDensity_nonneg {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) (x : Space d) : 0 ≤ mixtureDensity μ x :=
  integral_nonneg fun θ => (phi_pos (x - θ.val)).le

/-- The mixture law is a probability measure by proved density normalization. -/
instance mixtureMeasure_isProbabilityMeasure {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (mixtureMeasure μ) := by
  constructor
  rw [mixtureMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_mixtureDensity μ)
      (Filter.Eventually.of_forall (mixtureDensity_nonneg μ)), integral_mixtureDensity]
  norm_num

/-- Completing the square, as used to identify the terminal density. -/
theorem phi_mul_kernel {d : ℕ} (θ x : Space d) :
    phi x * kernel θ x 1 = phi (x - θ) := by
  unfold phi kernel
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  rw [norm_sub_sq_real, real_inner_comm θ x]
  ring

/-- The integrated Gaussian shift identity, with no conditional realization. -/
theorem phi_mul_partition {d : ℕ} {M : ℝ} (μ : Measure (Ball d M))
    (x : Space d) : phi x * partition μ x 1 = mixtureDensity μ x := by
  unfold partition mixtureDensity
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => phi_mul_kernel θ.val x

theorem kernel_le_of_nonneg_time {d : ℕ} {M t : ℝ}
    (θ : Ball d M) (x : Space d) (ht : 0 ≤ t) :
    kernel θ.val x t ≤ exp (M * ‖x‖) := by
  apply Real.exp_le_exp.mpr
  have hi := real_inner_le_norm θ.val x
  have hn := mul_le_mul_of_nonneg_right θ.property (norm_nonneg x)
  have hp : 0 ≤ t * ‖θ.val‖ ^ 2 / 2 := by positivity
  linarith

theorem kernel_lower_of_nonneg_time {d : ℕ} {M t : ℝ}
    (hM : 0 ≤ M) (θ : Ball d M) (x : Space d) (ht : 0 ≤ t) :
    exp (-M * ‖x‖ - t * M ^ 2 / 2) ≤ kernel θ.val x t := by
  apply Real.exp_le_exp.mpr
  have hi := (abs_le.mp (abs_real_inner_le_norm θ.val x)).1
  have hn := mul_le_mul_of_nonneg_right θ.property (norm_nonneg x)
  have hs : ‖θ.val‖ ^ 2 ≤ M ^ 2 := by nlinarith [θ.property, norm_nonneg θ.val]
  have hp := mul_le_mul_of_nonneg_left hs ht
  linarith

/-- Uniform domination valid for positive and negative time. -/
theorem kernel_le_abs_time {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (θ : Ball d M) (x : Space d) (t : ℝ) :
    kernel θ.val x t ≤ exp (M * ‖x‖ + |t| * M ^ 2 / 2) := by
  apply Real.exp_le_exp.mpr
  have hi := real_inner_le_norm θ.val x
  have hn := mul_le_mul_of_nonneg_right θ.property (norm_nonneg x)
  have hs : ‖θ.val‖ ^ 2 ≤ M ^ 2 := by nlinarith [θ.property, norm_nonneg θ.val]
  have ht := neg_abs_le t
  have hp := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖θ.val‖)
  have hq := mul_le_mul_of_nonneg_left hs (abs_nonneg t)
  linarith

theorem continuous_kernel_prior {d : ℕ} {M : ℝ} (x : Space d) (t : ℝ) :
    Continuous (fun θ : Ball d M => kernel θ.val x t) := by
  unfold kernel
  fun_prop

/-- Compact support gives genuine Bochner integrability for every real time. -/
theorem integrable_kernel {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (t : ℝ) :
    Integrable (fun θ => kernel θ.val x t) μ := by
  apply (integrable_const (exp (M * ‖x‖ + |t| * M ^ 2 / 2))).mono'
    (continuous_kernel_prior x t).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro θ
  rw [Real.norm_eq_abs, abs_of_pos (kernel_pos θ.val x t)]
  exact kernel_le_abs_time hM θ x t

theorem partition_pos {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (x : Space d) (t : ℝ) :
    0 < partition μ x t := by
  exact integral_exp_pos (integrable_kernel hM μ x t)

/-- The precise two-sided partition bounds in the regularity lemma, part (i). -/
theorem partition_bounds {d : ℕ} {M t : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (x : Space d) (ht : 0 ≤ t) :
    exp (-M * ‖x‖ - t * M ^ 2 / 2) ≤ partition μ x t ∧
      partition μ x t ≤ exp (M * ‖x‖) := by
  constructor
  · have h := integral_mono (integrable_const (exp (-M * ‖x‖ - t * M ^ 2 / 2)))
      (integrable_kernel hM μ x t) (fun θ => kernel_lower_of_nonneg_time hM θ x ht)
    simpa [partition] using h
  · have h := integral_mono (integrable_kernel hM μ x t)
      (integrable_const (exp (M * ‖x‖))) (fun θ => kernel_le_of_nonneg_time θ x ht)
    simpa [partition] using h

/-- The partition starts at one at the origin and zero time. -/
theorem partition_zero_zero {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    partition μ 0 0 = 1 := by
  simp [partition, kernel]

/-- Bounds for the log partition, which is well-defined everywhere. -/
theorem log_partition_bounds {d : ℕ} {M t : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (x : Space d) (ht : 0 ≤ t) :
    -M * ‖x‖ - t * M ^ 2 / 2 ≤ log (partition μ x t) ∧
      log (partition μ x t) ≤ M * ‖x‖ := by
  have hZ := partition_pos hM μ x t
  have hbounds := partition_bounds hM μ x ht
  exact ⟨(Real.le_log_iff_exp_le hZ).mpr hbounds.1,
    (Real.log_le_iff_le_exp hZ).mpr hbounds.2⟩

/-- Joint continuity is proved for the actual integral. -/
theorem continuous_partition {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    Continuous (fun p : Space d × ℝ => partition μ p.1 p.2) := by
  have hc : Continuous (fun q : (Space d × ℝ) × Ball d M =>
      kernel q.2.val q.1.1 q.1.2) := by
    unfold kernel
    fun_prop
  simpa [partition] using
    (continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ)

theorem continuous_phi (d : ℕ) : Continuous (fun x : Space d => phi x) := by
  unfold phi
  fun_prop

/-- The mixture is a continuous density, hence a Borel measurable one. -/
theorem continuous_mixtureDensity {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    Continuous (mixtureDensity μ) := by
  have heq : mixtureDensity μ = fun x => phi x * partition μ x 1 := by
    funext x
    exact (phi_mul_partition μ x).symm
  rw [heq]
  exact (continuous_phi d).mul
    ((continuous_partition μ).comp (continuous_id.prodMk continuous_const))

/-- Joint continuity of the logarithm uses the proved positive partition. -/
theorem continuous_log_partition {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    Continuous (fun p : Space d × ℝ => log (partition μ p.1 p.2)) := by
  exact (continuous_partition μ).log fun p => (partition_pos hM μ p.1 p.2).ne'

theorem mixtureDensity_pos {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (x : Space d) :
    0 < mixtureDensity μ x := by
  rw [← phi_mul_partition]
  exact mul_pos (phi_pos x) (partition_pos hM μ x 1)

/-- Integrability of the vector numerator in the posterior mean. -/
theorem integrable_kernel_smul {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (t : ℝ) :
    Integrable (fun θ : Ball d M => kernel θ.val x t • θ.val) μ := by
  have hc : Continuous (fun θ : Ball d M => kernel θ.val x t • θ.val) :=
    (continuous_kernel_prior x t).smul continuous_subtype_val
  apply ((integrable_kernel hM μ x t).const_mul M).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro θ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (kernel_pos θ.val x t)]
  calc
    kernel θ.val x t * ‖θ.val‖ ≤ kernel θ.val x t * M :=
      mul_le_mul_of_nonneg_left θ.property (kernel_pos θ.val x t).le
    _ = M * kernel θ.val x t := mul_comm _ _

/-- The bounded posterior drift is a jointly continuous deterministic function. -/
theorem continuous_posteriorMean {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    Continuous (fun p : Space d × ℝ => posteriorMean μ p.1 p.2) := by
  have hc : Continuous (fun q : (Space d × ℝ) × Ball d M =>
      kernel q.2.val q.1.1 q.1.2 • q.2.val) := by
    unfold kernel
    fun_prop
  have hnum : Continuous (fun p : Space d × ℝ =>
      ∫ θ : Ball d M, kernel θ.val p.1 p.2 • θ.val ∂μ) := by
    simpa using
      (continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ)
  exact ((continuous_partition μ).inv₀
    (fun p => (partition_pos hM μ p.1 p.2).ne')).smul hnum

/-- A proved posterior mean bound; no posterior bound is assumed. -/
theorem norm_posteriorMean_le {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (x : Space d) (t : ℝ) :
    ‖posteriorMean μ x t‖ ≤ M := by
  have hZ := partition_pos hM μ x t
  have hnum : ‖∫ θ : Ball d M, kernel θ.val x t • θ.val ∂μ‖ ≤ M * partition μ x t := by
    calc
      ‖∫ θ : Ball d M, kernel θ.val x t • θ.val ∂μ‖ ≤
          ∫ θ : Ball d M, M * kernel θ.val x t ∂μ := by
        apply norm_integral_le_of_norm_le ((integrable_kernel hM μ x t).const_mul M)
        apply Filter.Eventually.of_forall
        intro θ
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (kernel_pos θ.val x t)]
        calc
          kernel θ.val x t * ‖θ.val‖ ≤ kernel θ.val x t * M :=
            mul_le_mul_of_nonneg_left θ.property (kernel_pos θ.val x t).le
          _ = M * kernel θ.val x t := mul_comm _ _
      _ = M * partition μ x t := integral_const_mul _ _
  unfold posteriorMean
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hZ)]
  calc
    (partition μ x t)⁻¹ * ‖∫ θ : Ball d M, kernel θ.val x t • θ.val ∂μ‖ ≤
        (partition μ x t)⁻¹ * (M * partition μ x t) :=
      mul_le_mul_of_nonneg_left hnum (inv_pos.mpr hZ).le
    _ = M := by field_simp [ne_of_gt hZ]

/-- For two priors, their half-difference has the manuscript's bound `M`. -/
theorem norm_half_posteriorMean_sub_le {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Space d) (t : ℝ) :
    ‖(1 / 2 : ℝ) • (posteriorMean μ x t - posteriorMean ν x t)‖ ≤ M := by
  rw [norm_smul]
  have h₁ := norm_posteriorMean_le hM μ x t
  have h₂ := norm_posteriorMean_le hM ν x t
  have h₃ := norm_sub_le (posteriorMean μ x t) (posteriorMean ν x t)
  norm_num
  linarith

end GaussianComparison.GaussianModel
