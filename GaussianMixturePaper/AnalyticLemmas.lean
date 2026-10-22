import GaussianComparison.MeanScalingIdentities

/-!
Paper-facing analytic lemmas for version_final.pdf (22 October 2026).
The C¹ hypothesis in Lemma 2 is represented by a continuous function together
with a continuous gradient field and its pointwise HasGradientAt certificate.
-/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology InnerProductSpace
namespace GaussianMixturePaper
open GaussianComparison GaussianComparison.GaussianModel

variable {d : ℕ} {M : ℝ}

/-- The density's ordinary time derivative, identified without an assumption. -/
theorem density_time_derivative
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : ℝ) (x : Space d) :
    deriv (fun s => meanScaledDensity μ s x) t = phi x * scaledPartitionDot μ t x := by
  have hd := (scaledPartition_hasDerivAt μ t x).const_mul (phi x)
  have he : (fun s => meanScaledDensity μ s x) =
      (fun s => phi x * scaledPartition μ s x) := by
    funext s
    exact meanScaledDensity_eq_partition μ s x
  rw [he]
  exact hd.deriv

/-- Lemma 2, including absolute integrability of both sides of (A.3). -/
theorem lemma2_with_gradient_field (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ]
    (g : Space d → ℝ) (G : Space d → Space d)
    (hg : Continuous g) (hG : Continuous G)
    (hgrad : ∀ x, HasGradientAt g (G x) x)
    {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hbound : ∀ x, |g x| + ‖G x‖ ≤ L * exp (c * ‖x‖)) (t : ℝ) :
    Integrable (fun x => deriv (fun s => meanScaledDensity μ s x) t * g x) ∧
    Integrable (fun x => meanScaledDensity μ t x * ⟪G x, meanScaledPosterior μ t x⟫_ℝ) ∧
    (∫ x, deriv (fun s => meanScaledDensity μ s x) t * g x) =
      ∫ x, meanScaledDensity μ t x * ⟪G x, meanScaledPosterior μ t x⟫_ℝ := by
  have hgb : ExpGrowth (fun (_ : Unit) x => g x) := by
    refine ⟨L, c, hL, hc, fun _ x => ?_⟩
    simpa only [Real.norm_eq_abs] using (le_add_of_nonneg_right (norm_nonneg (G x))).trans (hbound x)
  have hGb : ExpGrowth (fun (_ : Unit) x => G x) := by
    exact ⟨L, c, hL, hc, fun _ x => (le_add_of_nonneg_left (abs_nonneg (g x))).trans (hbound x)⟩
  simp_rw [density_time_derivative]
  have he : (fun x => meanScaledDensity μ t x * ⟪G x, meanScaledPosterior μ t x⟫_ℝ) =
      (fun x => meanScaledDensity μ t x * ⟪meanScaledPosterior μ t x, G x⟫_ℝ) := by
    funext x; rw [real_inner_comm (G x)]
  rw [he]
  exact ⟨integrable_scaledPartitionDot_mul hM μ t hg hgb,
    integrable_meanScaledDensity_mul_inner hM μ t hG hGb,
    meanScaling_weak_derivative hM μ t g G hg hG hgrad hgb hGb⟩

/-- Lemma 2 in its manuscript C¹ form, using the canonical gradient. -/
theorem lemma2_gaussian_integration_by_parts (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ]
    (g : Space d → ℝ) (hg : ContDiff ℝ 1 g)
    {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hbound : ∀ x, |g x| + ‖gradient g x‖ ≤ L * exp (c * ‖x‖)) (t : ℝ) :
    Integrable (fun x => deriv (fun s => meanScaledDensity μ s x) t * g x) ∧
    Integrable (fun x => meanScaledDensity μ t x * ⟪gradient g x, meanScaledPosterior μ t x⟫_ℝ) ∧
    (∫ x, deriv (fun s => meanScaledDensity μ s x) t * g x) =
      ∫ x, meanScaledDensity μ t x * ⟪gradient g x, meanScaledPosterior μ t x⟫_ℝ := by
  apply lemma2_with_gradient_field hM μ g (gradient g) hg.continuous
  · exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
      (hg.continuous_fderiv (by decide))
  · intro x
    exact (hg.differentiable (by decide) x).hasGradientAt
  · exact hL
  · exact hc
  · exact hbound


section LikelihoodRatio
variable (hM : 0 ≤ M) (μ ν : Measure (Ball d M))
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

/-- Equation (A.40), uniformly over any bounded time interval. -/
theorem logRatio_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |scaledLogRatio μ ν t x| ≤ 2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2 := by
  have hμ := log_partition_bounds hM μ (t • x) (sq_nonneg t)
  have hν := log_partition_bounds hM ν (t • x) (sq_nonneg t)
  have hn : ‖t • x‖ ≤ T * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg x)
  have ht2 : t ^ 2 ≤ T ^ 2 := by
    nlinarith [sq_abs t, abs_nonneg t]
  have hb1 := mul_le_mul_of_nonneg_left hn hM
  have hb2 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg M)
  simp only [scaledLogRatio, scaledPartition]
  rw [Real.log_div
    (partition_pos hM μ _ _).ne' (partition_pos hM ν _ _).ne']
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Equation (A.41), for every real power, including zero and negative powers. -/
theorem ratio_rpow_hasGradientAt (α t : ℝ) (x : Space d) :
    HasGradientAt (fun y => (scaledRatio μ ν t y) ^ α)
      ((α * t * (scaledRatio μ ν t x) ^ α) • meanScaledGap μ ν t x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((scaledLogRatio_hasGradientAt hM μ ν t x).hasFDerivAt.const_smul α).exp
  convert! h using 1
  · funext y
    rw [Real.rpow_def_of_pos (scaledRatio_pos hM μ ν t y)]
    simp only [Pi.smul_apply, smul_eq_mul, scaledLogRatio, scaledRatio]
    rw [mul_comm]
  · ext v
    have he : exp (α * scaledLogRatio μ ν t x) = (scaledRatio μ ν t x) ^ α := by
      rw [Real.rpow_def_of_pos (scaledRatio_pos hM μ ν t x)]
      congr 1; exact mul_comm _ _
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, smul_eq_mul, Pi.smul_apply, he]
    ring

/-- Lemma 6(i), with the numerical constants displayed in (A.42). -/
theorem lemma6_rpow_growth (α : ℝ) {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T)
    (x : Space d) :
    |(scaledRatio μ ν t x) ^ α| +
      ‖(α * t * (scaledRatio μ ν t x) ^ α) • meanScaledGap μ ν t x‖ ≤
      ((1 + 2 * |α| * T * M) * exp (|α| * T ^ 2 * M ^ 2 / 2)) *
        exp (2 * |α| * T * M * ‖x‖) := by
  let R := (scaledRatio μ ν t x) ^ α
  have hR : 0 < R := Real.rpow_pos_of_pos (scaledRatio_pos hM μ ν t x) α
  have hgap := norm_meanScaledGap_le hM μ ν t x
  have hb := logRatio_bound hM μ ν hT ht x
  have hpow : R ≤ exp (|α| * (2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2)) := by
    dsimp [R]
    rw [Real.rpow_def_of_pos (scaledRatio_pos hM μ ν t x)]
    apply exp_le_exp.mpr
    calc
      log (scaledRatio μ ν t x) * α ≤ |log (scaledRatio μ ν t x) * α| := le_abs_self _
      _ = |α| * |scaledLogRatio μ ν t x| := by rw [abs_mul]; exact mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (abs_nonneg α)
  have hgrad : ‖(α * t * R) • meanScaledGap μ ν t x‖ ≤ 2 * |α| * T * M * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hR]
    calc
      |α| * |t| * R * ‖meanScaledGap μ ν t x‖ ≤ |α| * T * R * (2 * M) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg α)) hR.le
        · exact hgap
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  change |R| + ‖(α * t * R) • meanScaledGap μ ν t x‖ ≤ _
  rw [abs_of_pos hR]
  calc
    R + ‖(α * t * R) • meanScaledGap μ ν t x‖ ≤ (1 + 2 * |α| * T * M) * R := by linarith
    _ ≤ (1 + 2 * |α| * T * M) *
      exp (|α| * (2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by
      have heq : |α| * (2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2) =
          |α| * T ^ 2 * M ^ 2 / 2 + 2 * |α| * T * M * ‖x‖ := by ring
      rw [heq, exp_add]
      ring

/-- Lemma 6(ii), with the numerical constants displayed in (A.43). -/
theorem lemma6_log_growth {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |scaledLogRatio μ ν t x| + ‖t • meanScaledGap μ ν t x‖ ≤
      (1 + 2 * T * M + T ^ 2 * M ^ 2 / 2) * exp ‖x‖ := by
  have hb := logRatio_bound hM μ ν hT ht x
  have hg : ‖t • meanScaledGap μ ν t x‖ ≤ 2 * T * M := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖meanScaledGap μ ν t x‖ ≤ T * (2 * M) :=
        mul_le_mul ht (norm_meanScaledGap_le hM μ ν t x) (norm_nonneg _) hT
      _ = _ := by ring
  have hn := norm_nonneg x
  have he := Real.add_one_le_exp ‖x‖
  have hcoeff : 0 ≤ 1 + 2 * T * M + T ^ 2 * M ^ 2 / 2 := by positivity
  calc
    _ ≤ 2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2 + 2 * T * M := add_le_add hb hg
    _ ≤ (1 + 2 * T * M + T ^ 2 * M ^ 2 / 2) * (1 + ‖x‖) := by
      nlinarith [mul_nonneg (sq_nonneg T) (sq_nonneg M),
        mul_nonneg (mul_nonneg (sq_nonneg T) (sq_nonneg M)) hn]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [add_comm] using he) hcoeff

/-- The exact gradient equality (A.41) in canonical gradient notation. -/
theorem lemma6_gradient (α t : ℝ) (x : Space d) :
    gradient (fun y => (scaledRatio μ ν t y) ^ α) x =
      (α * t * (scaledRatio μ ν t x) ^ α) • meanScaledGap μ ν t x :=
  (ratio_rpow_hasGradientAt hM μ ν α t x).gradient

/-- The two bounds in Lemma 6, expressed with the actual gradients. -/
theorem lemma6 (α : ℝ) {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    (|(scaledRatio μ ν t x) ^ α| +
      ‖gradient (fun y => (scaledRatio μ ν t y) ^ α) x‖ ≤
      ((1 + 2 * |α| * T * M) * exp (|α| * T ^ 2 * M ^ 2 / 2)) *
        exp (2 * |α| * T * M * ‖x‖)) ∧
    (|scaledLogRatio μ ν t x| + ‖gradient (scaledLogRatio μ ν t) x‖ ≤
      (1 + 2 * T * M + T ^ 2 * M ^ 2 / 2) * exp ‖x‖) := by
  rw [lemma6_gradient hM μ ν α t x,
    (scaledLogRatio_hasGradientAt hM μ ν t x).gradient]
  exact ⟨lemma6_rpow_growth hM μ ν α hT ht x, lemma6_log_growth hM μ ν hT ht x⟩

end LikelihoodRatio
end GaussianMixturePaper
