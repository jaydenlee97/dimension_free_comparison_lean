import GaussianComparison.ElementaryTheorem31
import GaussianComparison.ElementaryTheorem32

/-!
# Theorem 1 of the October 22, 2026 manuscript

The priors are arbitrary probability measures on the closed-ball subtype
`Ball d M = {x : EuclideanSpace ℝ (Fin d) // ‖x‖ ≤ M}`. The densities are
the actual Gaussian convolution integrals. The squared Hellinger distance
uses the paper's convention, with no factor of one half.

This entry point assembles the two already proved deterministic comparisons
and the proved integrability conditions. It assumes no derivative formula,
analytic certificate, or comparison conclusion. Representing an ambient
supported measure on the ball subtype is a separate correspondence result.
-/

noncomputable section

open MeasureTheory Real
open GaussianComparison GaussianComparison.GaussianModel

namespace GaussianMixturePaper

/-- The exact two inequalities in Theorem 1, for probability priors represented
on the closed-ball subtype. In particular, the radius may equal zero. -/
theorem theorem1 {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (kl volume (mixtureDensity μ) (mixtureDensity ν) +
        kl volume (mixtureDensity ν) (mixtureDensity μ) ≤
      (2 * M ^ 2 + 4) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν)) ∧
    (max (chiSq volume (mixtureDensity μ) (mixtureDensity ν))
        (chiSq volume (mixtureDensity ν) (mixtureDensity μ)) ≤
      (18 * exp (4 * M ^ 2) - 2) *
        hellingerSq volume (mixtureDensity μ) (mixtureDensity ν)) :=
  ⟨elementary_gaussian_kl_comparison hM μ ν,
    elementary_gaussian_chiSq_max_comparison hM μ ν⟩

/-- Theorem 1 with an explicit validity certificate proving that all density
integrals are finite. The certificate is a conclusion, not a hypothesis. -/
theorem theorem1_with_finiteness {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    FiniteDivergences volume (mixtureDensity μ) (mixtureDensity ν) ∧
    (kl volume (mixtureDensity μ) (mixtureDensity ν) +
        kl volume (mixtureDensity ν) (mixtureDensity μ) ≤
      (2 * M ^ 2 + 4) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν)) ∧
    (max (chiSq volume (mixtureDensity μ) (mixtureDensity ν))
        (chiSq volume (mixtureDensity ν) (mixtureDensity μ)) ≤
      (18 * exp (4 * M ^ 2) - 2) *
        hellingerSq volume (mixtureDensity μ) (mixtureDensity ν)) :=
  ⟨finiteDivergences_mixture hM μ ν, theorem1 hM μ ν⟩

end GaussianMixturePaper
