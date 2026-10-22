import GaussianComparison.GaussianModel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Derivatives of the actual Gaussian partition function

All derivatives here are derivatives of the Bochner integral defined in
`GaussianModel`. Compactness supplies uniform domination in a parameter
neighborhood. No interchange of derivative and integral is assumed.
-/

noncomputable section

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace

namespace GaussianComparison.GaussianModel

instance ballT2Space (d : ℕ) (M : ℝ) : T2Space (Ball d M) :=
  inferInstanceAs (T2Space {θ : Space d // ‖θ‖ ≤ M})

/-- A compact-prior differentiation lemma with proved uniform domination. -/
theorem hasDerivAt_integral_compact_prior {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    {F F' : ℝ → Ball d M → ℝ}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ s θ, HasDerivAt (fun u : ℝ => F u θ) (F' s θ) s) (t : ℝ) :
    HasDerivAt (fun s => ∫ θ, F s θ ∂μ) (∫ θ, F' t θ ∂μ) t := by
  have hFt (s : ℝ) : Continuous (F s) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hF't (s : ℝ) : Continuous (F' s) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  have hint : Integrable (F t) μ := by
    simpa using (hFt t).continuousOn.integrableOn_compact isCompact_univ
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall t 1).prod (isCompact_univ (X := Ball d M))).bddAbove_image
      hF'.norm.continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall t 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t (by norm_num))
    (Filter.Eventually.of_forall fun s => (hFt s).aestronglyMeasurable) hint
    (hF't t).aestronglyMeasurable _ (integrable_const C) _).2
  · exact Filter.Eventually.of_forall fun θ s hs =>
      hC (Set.mem_image_of_mem (fun q : ℝ × Ball d M => ‖F' q.1 q.2‖)
        (show (s, θ) ∈ Metric.closedBall t 1 ×ˢ Set.univ from ⟨hs, Set.mem_univ θ⟩))
  · exact Filter.Eventually.of_forall fun θ s _ => hd s θ

/-- The ordinary time derivative of the kernel. -/
theorem kernel_hasDerivAt_time {d : ℕ} (θ x : Space d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => kernel θ x u) ((-‖θ‖ ^ 2 / 2) * kernel θ x t) t := by
  have h := ((((hasDerivAt_id t).mul_const (‖θ‖ ^ 2)).div_const 2).const_sub ⟪θ, x⟫_ℝ).exp
  simpa [kernel, mul_comm, neg_div] using h

/-- The time derivative is obtained by differentiating the actual integral. -/
theorem partition_hasDerivAt_time {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => partition μ x u)
      (∫ θ : Ball d M, (-‖θ.val‖ ^ 2 / 2) * kernel θ.val x t ∂μ) t := by
  refine hasDerivAt_integral_compact_prior μ
    (F := fun s θ => kernel θ.val x s)
    (F' := fun s θ => (-‖θ.val‖ ^ 2 / 2) * kernel θ.val x s) ?_ ?_ ?_ t
  · unfold Function.uncurry kernel
    fun_prop
  · unfold Function.uncurry kernel
    fun_prop
  · exact fun s θ => kernel_hasDerivAt_time θ.val x s

theorem deriv_partition_time {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (t : ℝ) :
    deriv (fun u : ℝ => partition μ x u) t =
      -(1 / 2 : ℝ) * ∫ θ : Ball d M, ‖θ.val‖ ^ 2 * kernel θ.val x t ∂μ := by
  rw [(partition_hasDerivAt_time μ x t).deriv, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by ring

/-- Directional derivative of the kernel along an arbitrary affine line. -/
theorem kernel_hasDerivAt_spatialLine {d : ℕ} (θ x v : Space d) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => kernel θ (x + u • v) t)
      (⟪θ, v⟫_ℝ * kernel θ (x + s • v) t) s := by
  have h := ((((hasDerivAt_id s).mul_const ⟪θ, v⟫_ℝ).const_add ⟪θ, x⟫_ℝ).sub_const
    (t * ‖θ‖ ^ 2 / 2)).exp
  simpa [kernel, inner_add_right, inner_smul_right, mul_comm] using h

/-- Weighted directional differentiation, reusable for higher derivatives. -/
theorem weightedPartition_hasDerivAt_spatialLine {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (w : Ball d M → ℝ)
    (hw : Continuous w) (x v : Space d) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ θ : Ball d M, w θ * kernel θ.val (x + u • v) t ∂μ)
      (∫ θ : Ball d M, (w θ * ⟪θ.val, v⟫_ℝ) * kernel θ.val (x + s • v) t ∂μ) s := by
  refine hasDerivAt_integral_compact_prior μ
    (F := fun s θ => w θ * kernel θ.val (x + s • v) t)
    (F' := fun s θ => (w θ * ⟪θ.val, v⟫_ℝ) * kernel θ.val (x + s • v) t) ?_ ?_ ?_ s
  · unfold Function.uncurry kernel
    fun_prop
  · unfold Function.uncurry kernel
    fun_prop
  · intro u θ
    simpa only [mul_assoc] using
      (kernel_hasDerivAt_spatialLine θ.val x v t u).const_mul (w θ)

/-- First spatial directional derivative of the actual partition function. -/
theorem partition_hasDerivAt_spatialLine {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x v : Space d) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => partition μ (x + u • v) t)
      (∫ θ : Ball d M, ⟪θ.val, v⟫_ℝ * kernel θ.val (x + s • v) t ∂μ) s := by
  simpa only [one_mul, partition] using
    weightedPartition_hasDerivAt_spatialLine μ (fun _ => 1) continuous_const x v t s

/-- Second spatial directional derivative of the actual partition function. -/
theorem deriv_deriv_partition_spatialLine {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x v : Space d) (t s : ℝ) :
    deriv (deriv (fun u : ℝ => partition μ (x + u • v) t)) s =
      ∫ θ : Ball d M, ⟪θ.val, v⟫_ℝ ^ 2 * kernel θ.val (x + s • v) t ∂μ := by
  have hfirst : deriv (fun u : ℝ => partition μ (x + u • v) t) =
      fun u : ℝ => ∫ θ : Ball d M, ⟪θ.val, v⟫_ℝ * kernel θ.val (x + u • v) t ∂μ := by
    funext u
    exact (partition_hasDerivAt_spatialLine μ x v t u).deriv
  rw [hfirst]
  have hw : Continuous (fun θ : Ball d M => ⟪θ.val, v⟫_ℝ) := by fun_prop
  simpa only [pow_two] using
    (weightedPartition_hasDerivAt_spatialLine μ (fun θ => ⟪θ.val, v⟫_ℝ) hw x v t s).deriv

/-- The coordinate formula for the Euclidean Laplacian, using actual second derivatives. -/
def coordinateLaplacian {d : ℕ} (f : Space d → ℝ) (x : Space d) : ℝ :=
  ∑ i : Fin d, deriv (deriv (fun s : ℝ =>
    f (x + s • EuclideanSpace.basisFun (Fin d) ℝ i))) 0

/-- The spatial Laplacian of the actual partition equals the second prior moment. -/
theorem coordinateLaplacian_partition {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (t : ℝ) :
    coordinateLaplacian (fun y => partition μ y t) x =
      ∫ θ : Ball d M, ‖θ.val‖ ^ 2 * kernel θ.val x t ∂μ := by
  unfold coordinateLaplacian
  simp_rw [deriv_deriv_partition_spatialLine, zero_smul, add_zero]
  have hi (i : Fin d) : Integrable
      (fun θ : Ball d M => ⟪θ.val, EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ ^ 2 *
        kernel θ.val x t) μ := by
    have hc : Continuous (fun θ : Ball d M =>
        ⟪θ.val, EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ ^ 2 * kernel θ.val x t) := by
      unfold kernel
      fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro θ
  simpa only [Finset.sum_mul] using congrArg (fun z : ℝ => z * kernel θ.val x t)
    ((EuclideanSpace.basisFun (Fin d) ℝ).sum_sq_inner_left θ.val)

/-- The backward heat equation, with a coordinate Laplacian of actual derivatives. -/
theorem partition_backward_heat {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (t : ℝ) :
    deriv (fun u => partition μ x u) t +
      (1 / 2 : ℝ) * coordinateLaplacian (fun y => partition μ y t) x = 0 := by
  rw [deriv_partition_time, coordinateLaplacian_partition]
  ring

/-- Spatial Fréchet differentiation under the compact-prior integral. -/
theorem hasFDerivAt_integral_compact_prior_space {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    {F : Space d → Ball d M → ℝ} {F' : Space d → Ball d M → Space d →L[ℝ] ℝ}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ y θ, HasFDerivAt (fun z => F z θ) (F' y θ) y) (x : Space d) :
    HasFDerivAt (fun y => ∫ θ, F y θ ∂μ) (∫ θ, F' x θ ∂μ) x := by
  have hFy (y : Space d) : Continuous (F y) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hF'y (y : Space d) : Continuous (F' y) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  have hint : Integrable (F x) μ := by
    simpa using (hFy x).continuousOn.integrableOn_compact isCompact_univ
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall x 1).prod (isCompact_univ (X := Ball d M))).bddAbove_image
      hF'.norm.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x (by norm_num))
    (Filter.Eventually.of_forall fun y => (hFy y).aestronglyMeasurable) hint
    (hF'y x).aestronglyMeasurable _ (integrable_const C) _
  · exact Filter.Eventually.of_forall fun θ y hy =>
      hC (Set.mem_image_of_mem (fun q : Space d × Ball d M => ‖F' q.1 q.2‖)
        (show (y, θ) ∈ Metric.closedBall x 1 ×ˢ Set.univ from ⟨hy, Set.mem_univ θ⟩))
  · exact Filter.Eventually.of_forall fun θ y _ => hd y θ

/-- The full spatial derivative of the exponential kernel. -/
theorem kernel_hasFDerivAt_space {d : ℕ} (θ x : Space d) (t : ℝ) :
    HasFDerivAt (fun y => kernel θ y t) (kernel θ x t • innerSL ℝ θ) x := by
  exact ((innerSL ℝ θ).hasFDerivAt.sub_const (t * ‖θ‖ ^ 2 / 2)).exp

/-- The full spatial derivative of the actual partition integral. -/
theorem partition_hasFDerivAt_space {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (t : ℝ) :
    HasFDerivAt (fun y => partition μ y t)
      (∫ θ : Ball d M, kernel θ.val x t • innerSL ℝ θ.val ∂μ) x := by
  refine hasFDerivAt_integral_compact_prior_space μ
    (F := fun y θ => kernel θ.val y t)
    (F' := fun y θ => kernel θ.val y t • innerSL ℝ θ.val) ?_ ?_ ?_ x
  · unfold Function.uncurry kernel
    fun_prop
  · unfold Function.uncurry kernel
    fun_prop
  · exact fun y θ => kernel_hasFDerivAt_space θ.val y t

/-- The gradient of `Z` is its actual first weighted moment. -/
theorem partition_hasGradientAt {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (x : Space d) (t : ℝ) :
    HasGradientAt (fun y => partition μ y t)
      (∫ θ : Ball d M, kernel θ.val x t • θ.val ∂μ) x := by
  have hc : Continuous (fun θ : Ball d M => kernel θ.val x t • innerSL ℝ θ.val) := by
    unfold kernel
    fun_prop
  have hi : Integrable (fun θ : Ball d M => kernel θ.val x t • innerSL ℝ θ.val) μ := by
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have heq : (∫ θ : Ball d M, kernel θ.val x t • innerSL ℝ θ.val ∂μ) =
      InnerProductSpace.toDual ℝ (Space d)
        (∫ θ : Ball d M, kernel θ.val x t • θ.val ∂μ) := by
    ext v
    rw [ContinuousLinearMap.integral_apply hi]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      InnerProductSpace.toDual_apply_apply]
    have h := (innerSL ℝ v).integral_comp_comm (integrable_kernel_smul hM μ x t)
    simpa only [innerSL_apply_apply, inner_smul_right, real_inner_comm v] using h
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [← heq]
  exact partition_hasFDerivAt_space μ x t

/-- The posterior mean is proved to be the score `∇ log Z`. -/
theorem log_partition_hasGradientAt {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (x : Space d) (t : ℝ) :
    HasGradientAt (fun y => log (partition μ y t)) (posteriorMean μ x t) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (partition_hasGradientAt hM μ x t).hasFDerivAt.log
    (partition_pos hM μ x t).ne'
  convert! h using 1
  ext v
  simp [posteriorMean, InnerProductSpace.toDual_apply_apply]

/-- Literal gradient identity for the manuscript score. -/
theorem gradient_log_partition {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (x : Space d) (t : ℝ) :
    gradient (fun y => log (partition μ y t)) x = posteriorMean μ x t :=
  (log_partition_hasGradientAt hM μ x t).gradient

end GaussianComparison.GaussianModel
