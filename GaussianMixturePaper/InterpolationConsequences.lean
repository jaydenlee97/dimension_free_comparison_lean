import GaussianMixturePaper.GlobalRegularity
import GaussianComparison.ElementaryKLCore

/-! Global Hellinger monotonicity stated just after Lemma 1, and the range
`D : ℝ → [0,2]` in Appendix A.3.6. -/
noncomputable section
open MeasureTheory Real Set
open GaussianComparison GaussianComparison.GaussianModel

namespace GaussianMixturePaper
variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem hellinger_interpolation_range (t : ℝ) :
    meanScalingHellinger μ ν t ∈ Icc (0 : ℝ) 2 :=
  ⟨hellingerSq_nonneg volume _ _,
    (finiteDivergences_meanScaled_global hM μ ν t).hellingerSq_le_two⟩

/-- The paper's monotonicity claim on the full nonnegative half-line. -/
theorem hellinger_interpolation_monotone :
    MonotoneOn (meanScalingHellinger μ ν) (Ici (0 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (contDiff_meanScalingHellinger hM μ ν).continuous.continuousOn
    ((contDiff_meanScalingHellinger hM μ ν).differentiable one_ne_zero).differentiableOn
  intro t ht
  rw [(meanScalingHellinger_hasDerivAt_global hM μ ν t).deriv]
  have ht0 : 0 ≤ t := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using ht)
  exact meanScalingHellingerRate_nonneg μ ν t ht0

end GaussianMixturePaper
