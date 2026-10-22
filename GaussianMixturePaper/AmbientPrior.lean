import GaussianComparison.ElementaryTheorem31
import GaussianComparison.ElementaryTheorem32

/-!
# Ambient priors and the paper's quantified theorem

The foundational development represents a prior on the closed ball as a measure
on its subtype. Here an arbitrary probability measure on Euclidean space, with
almost every point in that ball, is transported to the subtype. Equality of the
actual convolution integrals is proved; support is not an extra analytic axiom.
-/

noncomputable section
open MeasureTheory Real
open GaussianComparison GaussianComparison.GaussianModel

namespace GaussianMixturePaper

variable {d : ℕ} {M : ℝ}

/-- The closed-ball set in the ambient Euclidean space is measurable. -/
theorem measurableSet_priorBall : MeasurableSet {θ : Space d | ‖θ‖ ≤ M} :=
  isClosed_le continuous_norm continuous_const |>.measurableSet

/-- Restrict an ambient prior to the closed-ball subtype. -/
def ballPrior (μ : Measure (Space d)) : Measure (Ball d M) :=
  μ.comap Subtype.val

/-- A prior concentrated on the ball keeps its full probability mass. -/
theorem ballPrior_isProbabilityMeasure (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ θ ∂μ, ‖θ‖ ≤ M) : IsProbabilityMeasure (ballPrior (M := M) μ) := by
  have hr : ∀ᵐ θ ∂μ, θ ∈ Set.range
      (Subtype.val : {θ : Space d | ‖θ‖ ≤ M} → Space d) := by
    filter_upwards [hμ] with θ hθ
    exact ⟨⟨θ, hθ⟩, rfl⟩
  exact (MeasurableEmbedding.subtype_coe
    (measurableSet_priorBall (d := d) (M := M))).isProbabilityMeasure_comap hr

/-- Pushing the transported prior back into Euclidean space recovers the original. -/
theorem map_ballPrior (μ : Measure (Space d)) (hμ : ∀ᵐ θ ∂μ, ‖θ‖ ≤ M) :
    (ballPrior (M := M) μ).map Subtype.val = μ := by
  exact (map_comap_subtype_coe
    (measurableSet_priorBall (d := d) (M := M)) μ).trans
      (Measure.restrict_eq_self_of_ae_mem hμ)

/-- The density in the manuscript, with the prior on all of Euclidean space. -/
def ambientMixtureDensity (μ : Measure (Space d)) (x : Space d) : ℝ :=
  ∫ θ, phi (x - θ) ∂μ

/-- Transport to the ball does not change a convolution density. -/
theorem mixtureDensity_ballPrior (μ : Measure (Space d))
    (hμ : ∀ᵐ θ ∂μ, ‖θ‖ ≤ M) :
    mixtureDensity (ballPrior (M := M) μ) = ambientMixtureDensity μ := by
  funext x
  change (∫ θ : {θ : Space d // ‖θ‖ ≤ M}, phi (x - θ.val) ∂μ.comap Subtype.val) = _
  have he := integral_subtype_comap (μ := μ)
    (measurableSet_priorBall (d := d) (M := M)) (fun θ => phi (x - θ))
  have hr : μ.restrict {θ : Space d | ‖θ‖ ≤ M} = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  rw [hr] at he
  exact he

/-- Theorem 1 for ambient probability measures supported almost surely in the
closed radius-`M` ball, with explicit finiteness of all divergence expressions.
No derivative identities or comparison inequalities occur as hypotheses. -/
theorem theorem1_ambient (hM : 0 ≤ M)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ θ ∂μ, ‖θ‖ ≤ M) (hν : ∀ᵐ θ ∂ν, ‖θ‖ ≤ M) :
    FiniteDivergences volume (ambientMixtureDensity μ) (ambientMixtureDensity ν) ∧
    kl volume (ambientMixtureDensity μ) (ambientMixtureDensity ν) +
      kl volume (ambientMixtureDensity ν) (ambientMixtureDensity μ) ≤
      (2 * M ^ 2 + 4) *
        hellingerSq volume (ambientMixtureDensity μ) (ambientMixtureDensity ν) ∧
    max (chiSq volume (ambientMixtureDensity μ) (ambientMixtureDensity ν))
      (chiSq volume (ambientMixtureDensity ν) (ambientMixtureDensity μ)) ≤
      (18 * exp (4 * M ^ 2) - 2) *
        hellingerSq volume (ambientMixtureDensity μ) (ambientMixtureDensity ν) := by
  letI := ballPrior_isProbabilityMeasure μ hμ
  letI := ballPrior_isProbabilityMeasure ν hν
  rw [← mixtureDensity_ballPrior μ hμ, ← mixtureDensity_ballPrior ν hν]
  exact ⟨finiteDivergences_mixture hM _ _, elementary_gaussian_kl_comparison hM _ _,
    elementary_gaussian_chiSq_max_comparison hM _ _⟩

end GaussianMixturePaper
