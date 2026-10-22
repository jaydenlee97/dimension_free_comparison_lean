import GaussianComparison.Divergences
import GaussianComparison.GaussianModel

/-!
# Actual Gaussian mixtures have finite divergences

This bridge proves the validity conditions of `FiniteDivergences` for the actual
Gaussian convolution densities. It does not assume any stochastic realization,
Itô formula, clock identity, or comparison inequality.
-/

noncomputable section

open MeasureTheory Real

namespace GaussianComparison.GaussianModel

/-- A Gaussian radial envelope for the directed likelihood-ratio second moment.
The dimension enters only the normalizing density, not the exponent coefficient. -/
theorem mixture_ratio_square_bound {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Space d) :
    mixtureDensity μ x ^ 2 / mixtureDensity ν x ≤
      exp (M ^ 2 / 2) * (phi x * exp ((3 * M) * ‖x‖)) := by
  have hμ := partition_bounds (t := (1 : ℝ)) hM μ x (by norm_num)
  have hν := partition_bounds (t := (1 : ℝ)) hM ν x (by norm_num)
  have hμpos := partition_pos hM μ x 1
  have hνpos := partition_pos hM ν x 1
  have hφ := phi_pos x
  have hsq : partition μ x 1 ^ 2 ≤ exp (M * ‖x‖) ^ 2 := by
    nlinarith [hμ.2, Real.exp_pos (M * ‖x‖)]
  have hr : partition μ x 1 ^ 2 / partition ν x 1 ≤
      exp (M * ‖x‖) ^ 2 / exp (-M * ‖x‖ - 1 * M ^ 2 / 2) :=
    div_le_div₀ (sq_nonneg _) hsq (exp_pos _) hν.1
  have hexp : exp (M * ‖x‖) ^ 2 / exp (-M * ‖x‖ - 1 * M ^ 2 / 2) =
      exp (M ^ 2 / 2) * exp ((3 * M) * ‖x‖) := by
    rw [pow_two, ← exp_add, ← exp_sub, ← exp_add]
    congr 1
    ring
  rw [hexp] at hr
  have heq : mixtureDensity μ x ^ 2 / mixtureDensity ν x =
      phi x * (partition μ x 1 ^ 2 / partition ν x 1) := by
    rw [← phi_mul_partition μ x, ← phi_mul_partition ν x]
    field_simp [hφ.ne', hνpos.ne']
  rw [heq]
  calc
    phi x * (partition μ x 1 ^ 2 / partition ν x 1) ≤
        phi x * (exp (M ^ 2 / 2) * exp ((3 * M) * ‖x‖)) :=
      mul_le_mul_of_nonneg_left hr hφ.le
    _ = exp (M ^ 2 / 2) * (phi x * exp ((3 * M) * ‖x‖)) := by ring

/-- The actual ratio-square function is integrable, by the radial Gaussian bound. -/
theorem integrable_mixture_ratio_square {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun x : Space d => mixtureDensity μ x ^ 2 / mixtureDensity ν x) := by
  have hc : Continuous (fun x : Space d => mixtureDensity μ x ^ 2 / mixtureDensity ν x) :=
    ((continuous_mixtureDensity μ).pow 2).div (continuous_mixtureDensity ν)
      (fun x => (mixtureDensity_pos hM ν x).ne')
  apply ((integrable_phi_mul_exp_norm d (3 * M)).const_mul (exp (M ^ 2 / 2))).mono'
    hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (mixtureDensity_pos hM ν x).le)]
  exact mixture_ratio_square_bound hM μ ν x

/-- All finite-divergence validity conditions hold for compactly supported
Gaussian mixing distributions. In particular, these divergences are genuine
finite values rather than the zero assigned to undefined Bochner integrals. -/
theorem finiteDivergences_mixture {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    GaussianComparison.FiniteDivergences volume (mixtureDensity μ) (mixtureDensity ν) := by
  apply GaussianComparison.finiteDivergences_of_ratio_square volume
    (mixtureDensity μ) (mixtureDensity ν)
    (integrable_mixtureDensity μ) (integrable_mixtureDensity ν)
    (Filter.Eventually.of_forall (mixtureDensity_pos hM μ))
    (Filter.Eventually.of_forall (mixtureDensity_pos hM ν))
    (integral_mixtureDensity μ) (integral_mixtureDensity ν)
  · exact integrable_mixture_ratio_square hM μ ν
  · exact integrable_mixture_ratio_square hM ν μ

end GaussianComparison.GaussianModel
