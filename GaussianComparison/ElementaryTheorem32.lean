import GaussianComparison.MeanScalingChiComparison

/-! The unconditional elementary proof of manuscript Theorem 3.2. The import
closure contains deterministic Gaussian analysis and no stochastic comparison. -/
noncomputable section
open MeasureTheory Real
namespace GaussianComparison
open GaussianModel

theorem elementary_gaussian_chiSq_comparison {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    chiSq volume (mixtureDensity μ) (mixtureDensity ν) ≤
      (18 * exp (4 * M ^ 2) - 2) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) :=
  meanScaling_chiSq_comparison hM μ ν

theorem elementary_gaussian_chiSq_max_comparison {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    max (chiSq volume (mixtureDensity μ) (mixtureDensity ν))
      (chiSq volume (mixtureDensity ν) (mixtureDensity μ)) ≤
      (18 * exp (4 * M ^ 2) - 2) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  apply max_le
  · exact elementary_gaussian_chiSq_comparison hM μ ν
  · rw [hellingerSq_symm volume (mixtureDensity μ) (mixtureDensity ν)]
    exact elementary_gaussian_chiSq_comparison hM ν μ

/-- The exact quantified manuscript statement, checked against Theorem32Goal
by the scoped audit without importing its stochastic proof here. -/
theorem elementary_theorem32 :
    ∀ (d : ℕ) (M : ℝ), 0 < M →
    ∀ (μ ν : Measure (Ball d M)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      max (chiSq volume (mixtureDensity μ) (mixtureDensity ν))
        (chiSq volume (mixtureDensity ν) (mixtureDensity μ)) ≤
        (18 * exp (4 * M ^ 2) - 2) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  intro d M hM μ ν hμ hν
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure ν := hν
  exact elementary_gaussian_chiSq_max_comparison hM.le μ ν

end GaussianComparison
