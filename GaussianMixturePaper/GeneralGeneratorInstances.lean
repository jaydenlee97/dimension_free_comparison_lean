import GaussianMixturePaper.GeneralDeBruijn
import GaussianMixturePaper.DensityPDE
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Concrete admissibility proofs for the three generators in Section 3.
The generic de Bruijn theorem's C² and exponential-growth hypotheses are proved
here, including uniform bounds for the second generator derivatives. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology InnerProductSpace

namespace GaussianComparison.GaussianModel

theorem kl_positiveC2Generator : PositiveC2Generator klGenerator where
  first := by
    intro r hr
    rw [(klGenerator_hasDerivAt hr).deriv]
    exact klGenerator_hasDerivAt hr
  second := by
    intro r hr
    have he : deriv klGenerator =ᶠ[𝓝 r] log := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact (klGenerator_hasDerivAt hx).deriv
    rw [klGenerator_secondDeriv hr]
    exact (Real.hasDerivAt_log hr.ne').congr_of_eventuallyEq he
  continuous_second := by
    apply (continuousOn_id.inv₀ (fun r hr => ne_of_gt hr)).congr
    intro r hr
    exact klGenerator_secondDeriv hr

theorem hellinger_positiveC2Generator : PositiveC2Generator hellingerGenerator where
  first := by
    intro r hr
    rw [(hellingerGenerator_hasDerivAt hr).deriv]
    exact hellingerGenerator_hasDerivAt hr
  second := by
    intro r hr
    have he : deriv hellingerGenerator =ᶠ[𝓝 r] (fun x => 1 - (sqrt x)⁻¹) := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact (hellingerGenerator_hasDerivAt hx).deriv
    have hd := (hasDerivAt_const r (1 : ℝ)).sub
      ((Real.hasDerivAt_sqrt hr.ne').inv (sqrt_pos.mpr hr).ne')
    change HasDerivAt (fun x => 1 - (sqrt x)⁻¹) _ r at hd
    rw [hellingerGenerator_secondDeriv hr]
    convert! hd.congr_of_eventuallyEq he using 1
    have hs := sq_sqrt hr.le
    field_simp [hr.ne', (sqrt_pos.mpr hr).ne']
    nlinarith
  continuous_second := by
    have hc : ContinuousOn (fun r : ℝ => (2 * r * sqrt r)⁻¹) (Ioi 0) := by
      apply ((continuous_const.mul continuous_id).mul continuous_sqrt).continuousOn.inv₀
      intro r hr
      exact (mul_pos (mul_pos (by norm_num) hr) (sqrt_pos.mpr hr)).ne'
    apply hc.congr
    intro r hr
    exact hellingerGenerator_secondDeriv hr

theorem chiSq_positiveC2Generator : PositiveC2Generator chiSqGenerator where
  first := by
    intro r hr
    rw [(chiSqGenerator_hasDerivAt r).deriv]
    exact chiSqGenerator_hasDerivAt r
  second := by
    intro r hr
    have he : deriv chiSqGenerator = (fun x => 2 * (x - 1)) :=
      funext fun x => (chiSqGenerator_hasDerivAt x).deriv
    rw [chiSqGenerator_secondDeriv, he]
    convert! (((hasDerivAt_id r).sub_const 1).const_mul 2) using 1
    simp
  continuous_second := by
    have he : deriv (deriv chiSqGenerator) = (fun _ => (2 : ℝ)) :=
      funext chiSqGenerator_secondDeriv
    rw [he]
    exact continuousOn_const

/-- The three continuous extensions are convex on the closed nonnegative axis.
Their required C² property is asserted only on positive arguments. -/
theorem paperGenerator_convex (f : ℝ → ℝ) (hf : GaussianMixturePaper.IsPaperGenerator f) :
    ConvexOn ℝ (Ici 0) f := by
  have hc2 : PositiveC2Generator f := by
    rcases hf with rfl | rfl | rfl
    · exact kl_positiveC2Generator
    · exact hellinger_positiveC2Generator
    · exact chiSq_positiveC2Generator
  have hc : Continuous f := by
    rcases hf with rfl | rfl | rfl
    · exact (continuous_mul_log.sub continuous_id).add continuous_const
    · exact (continuous_sqrt.sub continuous_const).pow 2
    · exact (continuous_id.sub continuous_const).pow 2
  apply convexOn_of_deriv2_nonneg (convex_Ici 0) hc.continuousOn
  · intro r hr
    have hp : 0 < r := by simpa only [interior_Ici, mem_Ioi] using hr
    exact (hc2.first r hp).differentiableAt.differentiableWithinAt
  · intro r hr
    have hp : 0 < r := by simpa only [interior_Ici, mem_Ioi] using hr
    exact (hc2.second r hp).differentiableAt.differentiableWithinAt
  · intro r hr
    have hp : 0 < r := by simpa only [interior_Ici, mem_Ioi] using hr
    change 0 ≤ deriv (deriv f) r
    rcases hf with rfl | rfl | rfl
    · rw [klGenerator_secondDeriv hp]; positivity
    · rw [hellingerGenerator_secondDeriv hp]; positivity
    · rw [chiSqGenerator_secondDeriv]; norm_num

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem kl_localGeneratorGrowth : LocalGeneratorGrowth μ ν klGenerator where
  value := by
    intro T hT
    exact (((scaledRatio_growth hM hT μ ν).mul
      (scaledLogRatio_growth hM hT μ ν)).sub (scaledRatio_growth hM hT μ ν)).add
      (ExpGrowth.const 1)
  first := by
    intro T hT
    simp_rw [(klGenerator_hasDerivAt (scaledRatio_pos hM μ ν _ _)).deriv]
    exact scaledLogRatio_growth hM hT μ ν
  second := by
    intro T hT
    simp_rw [klGenerator_secondDeriv (scaledRatio_pos hM μ ν _ _)]
    simpa only [scaledRatio, inv_div] using scaledRatio_growth hM hT ν μ

theorem hellinger_localGeneratorGrowth : LocalGeneratorGrowth μ ν hellingerGenerator where
  value := by
    intro T hT
    have hs := scaledRootRatio_growth hM hT μ ν
    simpa only [hellingerGenerator, scaledRootRatio, pow_two] using
      (hs.sub (ExpGrowth.const 1)).mul (hs.sub (ExpGrowth.const 1))
  first := by
    intro T hT
    simp_rw [(hellingerGenerator_hasDerivAt (scaledRatio_pos hM μ ν _ _)).deriv]
    have he (s : {s : ℝ // |s| ≤ T}) (x : Space d) :
        (sqrt (scaledRatio μ ν s.val x))⁻¹ = scaledRootRatio ν μ s.val x := by
      rw [← sqrt_inv]
      unfold scaledRootRatio scaledRatio
      rw [inv_div]
    simp_rw [he]
    exact (ExpGrowth.const 1).sub (scaledRootRatio_growth hM hT ν μ)
  second := by
    intro T hT
    simp_rw [hellingerGenerator_secondDeriv (scaledRatio_pos hM μ ν _ _)]
    have he (s : {s : ℝ // |s| ≤ T}) (x : Space d) :
        (2 * scaledRatio μ ν s.val x * sqrt (scaledRatio μ ν s.val x))⁻¹ =
          (2 : ℝ)⁻¹ * scaledRatio ν μ s.val x * scaledRootRatio ν μ s.val x := by
      have hr : scaledRatio ν μ s.val x = (scaledRatio μ ν s.val x)⁻¹ := by
        unfold scaledRatio
        rw [inv_div]
      rw [scaledRootRatio, hr, sqrt_inv]
      simp only [mul_inv_rev]
      ring
    simp_rw [he]
    exact ((ExpGrowth.const (2 : ℝ)⁻¹).mul (scaledRatio_growth hM hT ν μ)).mul
      (scaledRootRatio_growth hM hT ν μ)

theorem chiSq_localGeneratorGrowth : LocalGeneratorGrowth μ ν chiSqGenerator where
  value := by
    intro T hT
    have hr := scaledRatio_growth hM hT μ ν
    simpa only [chiSqGenerator, pow_two] using
      (hr.sub (ExpGrowth.const 1)).mul (hr.sub (ExpGrowth.const 1))
  first := by
    intro T hT
    simp_rw [(chiSqGenerator_hasDerivAt _).deriv]
    exact (ExpGrowth.const 2).mul ((scaledRatio_growth hM hT μ ν).sub (ExpGrowth.const 1))
  second := by
    intro T hT
    simp_rw [chiSqGenerator_secondDeriv]
    exact ExpGrowth.const 2

/-- All analytic hypotheses of the generic theorem hold for each paper generator. -/
theorem paperGenerator_admissible (f : ℝ → ℝ) (hf : GaussianMixturePaper.IsPaperGenerator f) :
    PositiveC2Generator f ∧ LocalGeneratorGrowth μ ν f := by
  rcases hf with rfl | rfl | rfl
  · exact ⟨kl_positiveC2Generator, kl_localGeneratorGrowth hM μ ν⟩
  · exact ⟨hellinger_positiveC2Generator, hellinger_localGeneratorGrowth hM μ ν⟩
  · exact ⟨chiSq_positiveC2Generator, chiSq_localGeneratorGrowth hM μ ν⟩

/-- Equation (3.3) for all three generators via the generic integration-by-parts
proof, with the regularity and growth certificates constructed above. -/
theorem paperGenerator_general_deBruijn (f : ℝ → ℝ)
    (hf : GaussianMixturePaper.IsPaperGenerator f) (s : ℝ) :
    s * deriv (fun r => densityFDivergence volume (meanScaledDensity μ r)
      (meanScaledDensity ν r) f) s = Matrix.trace (generatorFisherMatrix μ ν s f) := by
  obtain ⟨hc, hg⟩ := paperGenerator_admissible hM μ ν f hf
  exact general_deBruijn_matrix hM μ ν hc hg s

end GaussianComparison.GaussianModel
