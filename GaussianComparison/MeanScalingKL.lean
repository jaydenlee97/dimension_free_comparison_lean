import GaussianComparison.MeanScaling

/-!
# Mean-scaling KL: finite rates and calculus assembly

The actual density and posterior gap define both rates. Their integrability,
nonnegativity and comparison are proved here. The calculus assembly takes
the two divergence derivative identities and endpoint continuity as explicit
hypotheses, discharged in `ElementaryTheorem31.lean` by the analytic results of
`MeanScalingDivergenceCalculus.lean` and `MeanScalingIdentities.lean`.
-/

noncomputable section

open MeasureTheory Real Set

namespace GaussianComparison.GaussianModel

def meanScalingKLRate {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  s * ∫ x, (meanScaledDensity μ s x + meanScaledDensity ν s x) *
    ‖meanScaledGap μ ν s x‖ ^ 2

def meanScalingHellingerRate {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  s / 2 * ∫ x, sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) *
    ‖meanScaledGap μ ν s x‖ ^ 2

/-- A bounded posterior gap preserves integrability of a continuous weight. -/
theorem integrable_mul_meanScaledGap_sq {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) {f : Space d → ℝ} (hf : Integrable f) (hfc : Continuous f) :
    Integrable (fun x => f x * ‖meanScaledGap μ ν s x‖ ^ 2) := by
  have hgap : Continuous (fun x : Space d => meanScaledGap μ ν s x) :=
    continuous_meanScaledGap_space hM μ ν s
  apply (hf.norm.const_mul (4 * M ^ 2)).mono' (hfc.mul (hgap.norm.pow 2)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖f x * ‖meanScaledGap μ ν s x‖ ^ 2‖ ≤ 4 * M ^ 2 * ‖f x‖
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  have h := mul_le_mul_of_nonneg_left (sq_norm_meanScaledGap_le hM μ ν s x)
    (norm_nonneg (f x))
  simpa only [mul_comm] using h

theorem integrable_meanScalingKLRate_integrand {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (hs : |s| ≤ 1) :
    Integrable (fun x => (meanScaledDensity μ s x + meanScaledDensity ν s x) *
      ‖meanScaledGap μ ν s x‖ ^ 2) := by
  apply integrable_mul_meanScaledGap_sq hM μ ν s
    ((integrable_meanScaledDensity μ s hs).add (integrable_meanScaledDensity ν s hs))
  exact (continuous_meanScaledDensity_space μ s).add (continuous_meanScaledDensity_space ν s)

theorem integrable_meanScalingHellingerRate_integrand {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (hs : |s| ≤ 1) :
    Integrable (fun x => sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) *
      ‖meanScaledGap μ ν s x‖ ^ 2) := by
  apply integrable_mul_meanScaledGap_sq hM μ ν s
    (finiteDivergences_meanScaled hM μ ν s hs).integrable_affinity
  exact ((continuous_meanScaledDensity_space μ s).mul
    (continuous_meanScaledDensity_space ν s)).sqrt

theorem meanScalingHellingerRate_nonneg {d : ℕ} {M : ℝ}
    (μ ν : Measure (Ball d M)) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ meanScalingHellingerRate μ ν s := by
  apply mul_nonneg (div_nonneg hs (by norm_num))
  exact integral_nonneg fun x => mul_nonneg (sqrt_nonneg _) (sq_nonneg _)

/-- The pointwise split integrated against Euclidean volume. Every integral
used in linearity and monotonicity is proved integrable before it is used. -/
theorem meanScaling_rate_bound {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (hs : s ∈ Icc 0 1) :
    meanScalingKLRate μ ν s ≤
      4 * M ^ 2 * s * meanScalingHellinger μ ν s + 4 * meanScalingHellingerRate μ ν s := by
  have habs : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hfinite := finiteDivergences_meanScaled hM μ ν s habs
  have hJ := integrable_meanScalingKLRate_integrand hM μ ν s habs
  have hA := integrable_meanScalingHellingerRate_integrand hM μ ν s habs
  have hD := hfinite.integrable_hellingerSq
  have hpoint : ∀ᵐ x : Space d ∂volume,
      (meanScaledDensity μ s x + meanScaledDensity ν s x) * ‖meanScaledGap μ ν s x‖ ^ 2 ≤
      4 * M ^ 2 * (sqrt (meanScaledDensity μ s x) - sqrt (meanScaledDensity ν s x)) ^ 2 +
        2 * (sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) *
          ‖meanScaledGap μ ν s x‖ ^ 2) := by
    apply Filter.Eventually.of_forall
    intro x
    simpa only [mul_assoc] using ElementaryKL.density_weight_split_bound
      (meanScaledDensity_pos hM μ s x).le (meanScaledDensity_pos hM ν s x).le
      (sq_norm_meanScaledGap_le hM μ ν s x)
  have hi := integral_mono_ae hJ ((hD.const_mul (4 * M ^ 2)).add (hA.const_mul 2)) hpoint
  have hadd := integral_add (hD.const_mul (4 * M ^ 2)) (hA.const_mul 2)
  simp only [Pi.add_apply] at hi hadd
  rw [hadd, integral_const_mul, integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left hi hs.1
  unfold meanScalingKLRate meanScalingHellingerRate meanScalingHellinger hellingerSq
  nlinarith

/-- Calculus assembly for the actual Gaussian interpolation. The two
`HasDerivAt` hypotheses and continuity of the divergence curves are proved
separately and discharged by `elementary_gaussian_kl_comparison`. -/
theorem meanScaling_kl_comparison_of_derivatives {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hJcont : ContinuousOn (meanScalingJeffreys μ ν) (Icc 0 1))
    (hDcont : ContinuousOn (meanScalingHellinger μ ν) (Icc 0 1))
    (hJder : ∀ s ∈ Ioo 0 1, HasDerivAt (meanScalingJeffreys μ ν) (meanScalingKLRate μ ν s) s)
    (hDder : ∀ s ∈ Ioo 0 1, HasDerivAt (meanScalingHellinger μ ν)
      (meanScalingHellingerRate μ ν s) s) :
    kl volume (mixtureDensity μ) (mixtureDensity ν) +
      kl volume (mixtureDensity ν) (mixtureDensity μ) ≤
      (2 * M ^ 2 + 4) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  have h := ElementaryKL.kl_comparison_of_derivative_bound M
    (meanScalingJeffreys μ ν) (meanScalingHellinger μ ν)
    (meanScalingKLRate μ ν) (meanScalingHellingerRate μ ν)
    hJcont hDcont hJder hDder
    (fun s hs => meanScalingHellingerRate_nonneg μ ν s hs.1.le)
    (fun s hs => meanScaling_rate_bound hM μ ν s ⟨hs.1.le, hs.2.le⟩)
    (meanScalingJeffreys_zero μ ν) (meanScalingHellinger_zero μ ν)
  simpa only [meanScalingJeffreys_one, meanScalingHellinger_one] using h

end GaussianComparison.GaussianModel
