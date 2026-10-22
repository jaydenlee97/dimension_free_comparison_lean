import GaussianComparison.MeanScalingIntegration

/-! Lemma 5: exact density envelopes, time and space derivatives, and joint
smoothness of the mean-scaling Gaussian mixtures. -/

noncomputable section
open MeasureTheory Real Set
open scoped InnerProductSpace ContDiff
open GaussianComparison GaussianComparison.GaussianModel

namespace GaussianMixturePaper

variable {d : ℕ} {M : ℝ}

/-- The envelope coefficient in equation (A.18). -/
def densityTimeEnvelope (M T : ℝ) (x : Space d) : ℝ := M * ‖x‖ + T * M ^ 2

/-- The exact local two-sided envelope (A.19). -/
theorem density_envelopes (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ]
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    phi x * exp (-T * M * ‖x‖ - T ^ 2 * M ^ 2 / 2) ≤ meanScaledDensity μ t x ∧
      meanScaledDensity μ t x ≤ phi x * exp (T * M * ‖x‖) := by
  have hp := partition_bounds hM μ (t • x) (sq_nonneg t)
  have hn : M * ‖t • x‖ ≤ T * M * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_right ht (mul_nonneg hM (norm_nonneg x))]
  have hs : t ^ 2 ≤ T ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have hsM := mul_le_mul_of_nonneg_right hs (sq_nonneg M)
  rw [meanScaledDensity_eq_partition]
  constructor
  · apply mul_le_mul_of_nonneg_left _ (phi_pos x).le
    exact (exp_le_exp.mpr (by linarith)).trans hp.1
  · apply mul_le_mul_of_nonneg_left _ (phi_pos x).le
    exact hp.2.trans (exp_le_exp.mpr hn)

/-- The derivative formula (A.20). -/
theorem density_hasDerivAt_time
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (t : ℝ) (x : Space d) :
    HasDerivAt (fun s => meanScaledDensity μ s x)
      (∫ θ : Ball d M, (⟪θ.val, x⟫_ℝ - t * ‖θ.val‖ ^ 2) *
        phi (x - t • θ.val) ∂μ) t :=
  meanScaledDensity_hasDerivAt μ x t

/-- Equation (A.20) in terms of Lean's derivative operator. -/
theorem density_deriv_time
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (t : ℝ) (x : Space d) :
    deriv (fun s => meanScaledDensity μ s x) t =
      ∫ θ : Ball d M, (⟪θ.val, x⟫_ℝ - t * ‖θ.val‖ ^ 2) *
        phi (x - t • θ.val) ∂μ :=
  (density_hasDerivAt_time μ t x).deriv

theorem density_time_weight_bound (hM : 0 ≤ M) {T t : ℝ} (hT : 0 ≤ T)
    (ht : |t| ≤ T) (θ : Ball d M) (x : Space d) :
    |⟪θ.val, x⟫_ℝ - t * ‖θ.val‖ ^ 2| ≤ densityTimeEnvelope M T x := by
  have hθ : ‖θ.val‖ ^ 2 ≤ M ^ 2 := by nlinarith [θ.property, norm_nonneg θ.val]
  calc
    _ ≤ |⟪θ.val, x⟫_ℝ| + |t * ‖θ.val‖ ^ 2| := abs_sub _ _
    _ ≤ ‖θ.val‖ * ‖x‖ + |t| * ‖θ.val‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖θ.val‖)]
      exact add_le_add (abs_real_inner_le_norm θ.val x) le_rfl
    _ ≤ M * ‖x‖ + T * M ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_right θ.property (norm_nonneg _))
        (mul_le_mul ht hθ (sq_nonneg _) hT)
    _ = _ := rfl

/-- The local time-derivative bound (A.21). -/
theorem density_deriv_time_bound (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ]
    {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |deriv (fun s => meanScaledDensity μ s x) t| ≤
      densityTimeEnvelope M T x * meanScaledDensity μ t x := by
  rw [density_deriv_time]
  let f := fun θ : Ball d M => (⟪θ.val, x⟫_ℝ - t * ‖θ.val‖ ^ 2) * phi (x - t • θ.val)
  have hc : Continuous f := by dsimp [f, phi]; fun_prop
  have hg : Continuous (fun θ : Ball d M => densityTimeEnvelope M T x * phi (x - t • θ.val)) := by
    unfold phi; fun_prop
  have hi : Integrable (fun θ : Ball d M => ‖f θ‖) μ := by
    simpa using hc.norm.continuousOn.integrableOn_compact isCompact_univ
  have hj : Integrable (fun θ : Ball d M => densityTimeEnvelope M T x * phi (x - t • θ.val)) μ := by
    simpa using hg.continuousOn.integrableOn_compact isCompact_univ
  calc
    _ = ‖∫ θ, f θ ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ θ, ‖f θ‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ : Ball d M, densityTimeEnvelope M T x * phi (x - t • θ.val) ∂μ := by
      apply integral_mono hi hj
      intro θ
      dsimp [f]
      rw [abs_mul, abs_of_pos (phi_pos _)]
      exact mul_le_mul_of_nonneg_right (density_time_weight_bound hM hT ht θ x) (phi_pos _).le
    _ = densityTimeEnvelope M T x * meanScaledDensity μ t x := integral_const_mul _ _

/-- The spatial gradient in (A.22), expressed as a genuine vector integral. -/
theorem density_hasGradientAt_space
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (t : ℝ) (x : Space d) :
    HasGradientAt (meanScaledDensity μ t)
      (-(∫ θ : Ball d M, phi (x - t • θ.val) • (x - t • θ.val) ∂μ)) x := by
  let F' := fun (y : Space d) (θ : Ball d M) =>
    (-phi (y - t • θ.val)) • innerSL ℝ (y - t • θ.val)
  have hF' : Continuous F'.uncurry := by dsimp [F', phi]; fun_prop
  have hd := hasFDerivAt_integral_compact_prior_space μ
    (F := fun y θ => phi (y - t • θ.val)) (F' := F')
    (by unfold Function.uncurry phi; fun_prop) hF'
    (fun y θ => by
      convert! (phi_hasFDerivAt (y - t • θ.val)).comp y
        ((hasFDerivAt_id y).sub_const (t • θ.val)) using 1
      ) x
  have hi : Integrable (F' x) μ := by
    have hc : Continuous (F' x) := by dsimp [F', phi]; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have hv : Integrable (fun θ : Ball d M => phi (x - t • θ.val) • (x - t • θ.val)) μ := by
    have hc : Continuous (fun θ : Ball d M => phi (x - t • θ.val) • (x - t • θ.val)) := by
      unfold phi; fun_prop
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hd using 1
  ext v
  rw [ContinuousLinearMap.integral_apply hi]
  have he := (innerSL ℝ v).integral_comp_comm hv
  simp only [F', smul_apply, innerSL_apply_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, inner_neg_left] at *
  rw [real_inner_comm v _, ← he, ← integral_neg]
  simp only [real_inner_smul_right, neg_mul, real_inner_comm v]

theorem density_gradient_space
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (t : ℝ) (x : Space d) :
    gradient (meanScaledDensity μ t) x =
      -(∫ θ : Ball d M, phi (x - t • θ.val) • (x - t • θ.val) ∂μ) :=
  (density_hasGradientAt_space μ t x).gradient

/-- In fact the interpolated density is jointly infinitely differentiable. -/
theorem density_contDiff_joint
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    ContDiff ℝ ∞ (fun p : ℝ × Space d => meanScaledDensity μ p.1 p.2) := by
  simp_rw [meanScaledDensity_eq_partition]
  have hphi : ContDiff ℝ ∞ (fun x : Space d => phi x) := by
    unfold phi
    exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const 2).exp)
  exact (hphi.comp contDiff_snd).mul ((partition_contDiff_joint μ).comp
    ((contDiff_fst.smul contDiff_snd).prodMk (contDiff_fst.pow 2)))

/-- Lemma 5(iv), retaining precisely the requested C1 regularity. -/
theorem density_contDiff_one
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    ContDiff ℝ 1 (fun p : ℝ × Space d => meanScaledDensity μ p.1 p.2) :=
  (density_contDiff_joint μ).of_le (by simp)

end GaussianMixturePaper
