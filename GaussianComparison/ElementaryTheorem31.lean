import GaussianComparison.MeanScalingIdentities

/-! The unconditional elementary proof of the KL comparison for Gaussian
mixtures. Its local import closure uses only deterministic analysis. -/
noncomputable section
open MeasureTheory
namespace GaussianComparison
open GaussianModel

/-- Theorem 3.1, proved by scaling the means, ordinary differentiation and
Gaussian integration by parts. No stochastic realization is used. -/
theorem elementary_gaussian_kl_comparison {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    kl volume (mixtureDensity μ) (mixtureDensity ν) +
      kl volume (mixtureDensity ν) (mixtureDensity μ) ≤
        (2 * M ^ 2 + 4) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  exact meanScaling_kl_comparison_of_derivatives hM μ ν
    (continuous_meanScalingJeffreys hM μ ν).continuousOn
    (continuousOn_meanScalingHellinger hM μ ν)
    (meanScalingJeffreys_hasDerivAt hM μ ν)
    (meanScalingHellinger_hasDerivAt hM μ ν)

/-- The exact quantified manuscript statement. The audit checks that this
declaration has the existing `Theorem31Goal` type by definitional equality. -/
theorem elementary_theorem31 :
    ∀ (d : ℕ) (M : ℝ), 0 < M →
    ∀ (μ ν : Measure (Ball d M)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      kl volume (mixtureDensity μ) (mixtureDensity ν) +
        kl volume (mixtureDensity ν) (mixtureDensity μ) ≤
          (2 * M ^ 2 + 4) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  intro d M hM μ ν hμ hν
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure ν := hν
  exact elementary_gaussian_kl_comparison hM.le μ ν

end GaussianComparison
