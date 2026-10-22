import GaussianMixturePaper.Theorem1
import GaussianMixturePaper.Sharpness
import GaussianMixturePaper.Identifiability
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Optimal comparison constants in Remark 1

The supremum ranges over every finite dimension and every pair of distinct
probability priors on the closed radius-`M` ball. Results below require `M > 0`,
so the explicit one-dimensional example makes each ratio set nonempty.
-/
noncomputable section
open MeasureTheory Real Set Filter Asymptotics
open scoped Topology
open GaussianComparison GaussianComparison.GaussianModel

namespace GaussianMixturePaper

def jeffreysRatio {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) : ℝ :=
  (kl volume (mixtureDensity μ) (mixtureDensity ν) +
    kl volume (mixtureDensity ν) (mixtureDensity μ)) /
    hellingerSq volume (mixtureDensity μ) (mixtureDensity ν)

def chiSqMaxRatio {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) : ℝ :=
  max (chiSq volume (mixtureDensity μ) (mixtureDensity ν))
    (chiSq volume (mixtureDensity ν) (mixtureDensity μ)) /
    hellingerSq volume (mixtureDensity μ) (mixtureDensity ν)

def klRatioSet (M : ℝ) : Set ℝ :=
  {r | ∃ (d : ℕ) (μ ν : Measure (Ball d M)), IsProbabilityMeasure μ ∧
    IsProbabilityMeasure ν ∧ μ ≠ ν ∧ r = jeffreysRatio μ ν}

def chiSqRatioSet (M : ℝ) : Set ℝ :=
  {r | ∃ (d : ℕ) (μ ν : Measure (Ball d M)), IsProbabilityMeasure μ ∧
    IsProbabilityMeasure ν ∧ μ ≠ ν ∧ r = chiSqMaxRatio μ ν}

/-- Every admissible pair in the optimal-constant suprema has a strictly
positive denominator; the quotients are genuine ratios of divergences. -/
theorem optimal_constant_denominator_pos {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hne : μ ≠ ν) :
    0 < hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) :=
  hellingerSq_mixture_pos hM μ ν hne

/-- `C_KL(M)` in equation (1.3). -/
def optimalKL (M : ℝ) : ℝ := sSup (klRatioSet M)

/-- `C_chi²(M)` in equation (1.3). -/
def optimalChiSq (M : ℝ) : ℝ := sSup (chiSqRatioSet M)

def klExampleRatio (M : ℝ) : ℝ := 2 * M ^ 2 / (1 - exp (-M ^ 2 / 2))

def chiSqExampleRatio (M : ℝ) : ℝ :=
  (exp (4 * M ^ 2) - 1) / (2 * (1 - exp (-M ^ 2 / 2)))

theorem jeffreysRatio_le {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    jeffreysRatio μ ν ≤ 2 * M ^ 2 + 4 := by
  unfold jeffreysRatio
  by_cases hz : hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) = 0
  · rw [hz, div_zero]
    positivity
  · exact (div_le_iff₀ (lt_of_le_of_ne
      (hellingerSq_nonneg volume _ _) (Ne.symm hz))).mpr (theorem1 hM μ ν).1

theorem chiSqMaxRatio_le {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    chiSqMaxRatio μ ν ≤ 18 * exp (4 * M ^ 2) - 2 := by
  unfold chiSqMaxRatio
  by_cases hz : hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) = 0
  · rw [hz, div_zero]
    have he : 1 ≤ exp (4 * M ^ 2) := one_le_exp (by positivity)
    linarith
  · exact (div_le_iff₀ (lt_of_le_of_ne
      (hellingerSq_nonneg volume _ _) (Ne.symm hz))).mpr (theorem1 hM μ ν).2

theorem klRatioSet_bddAbove {M : ℝ} (hM : 0 ≤ M) : BddAbove (klRatioSet M) := by
  refine ⟨2 * M ^ 2 + 4, ?_⟩
  rintro r ⟨d, μ, ν, hμ, hν, _, rfl⟩
  letI := hμ
  letI := hν
  exact jeffreysRatio_le hM μ ν

theorem chiSqRatioSet_bddAbove {M : ℝ} (hM : 0 ≤ M) : BddAbove (chiSqRatioSet M) := by
  refine ⟨18 * exp (4 * M ^ 2) - 2, ?_⟩
  rintro r ⟨d, μ, ν, hμ, hν, _, rfl⟩
  letI := hμ
  letI := hν
  exact chiSqMaxRatio_le hM μ ν

/-- The two opposite point masses give members of the exact ratio sets.
Distinctness follows directly from their strictly positive Hellinger distance. -/
theorem sharpness_ratios_mem {M : ℝ} (hM : 0 < M) :
    klExampleRatio M ∈ klRatioSet M ∧ chiSqExampleRatio M ∈ chiSqRatioSet M := by
  let a : Ball 1 M := ⟨sharpnessMean M, (norm_sharpnessMean hM.le).le⟩
  let b : Ball 1 M := ⟨-sharpnessMean M, by rw [norm_neg, norm_sharpnessMean hM.le]⟩
  let μ : Measure (Ball 1 M) := Measure.dirac a
  let ν : Measure (Ball 1 M) := Measure.dirac b
  have hp : mixtureDensity μ = fun x => phi (x - sharpnessMean M) :=
    mixtureDensity_dirac_fun a
  have hq : mixtureDensity ν = fun x => phi (x + sharpnessMean M) := by
    simpa only [ν, b, sub_neg_eq_add] using mixtureDensity_dirac_fun b
  have hforms := remark1_gaussian_formulas hM.le
  dsimp at hforms
  have hH : hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) =
      2 * (1 - exp (-M ^ 2 / 2)) := by rw [hp, hq]; exact hforms.2.2
  have hne : μ ≠ ν := by
    intro he
    rw [he, hellingerSq_self] at hH
    have := remark1_hellinger_denominator_pos hM
    linarith
  have hkl : klExampleRatio M = jeffreysRatio μ ν := by
    unfold jeffreysRatio klExampleRatio
    rw [hp, hq, hforms.1, hforms.2.2]
    have hden : 1 - exp (-M ^ 2 / 2) ≠ 0 := by
      have := remark1_hellinger_denominator_pos hM
      linarith
    field_simp
    ring
  have hchi : chiSqExampleRatio M = chiSqMaxRatio μ ν := by
    unfold chiSqMaxRatio chiSqExampleRatio
    rw [hp, hq, hforms.2.1, hforms.2.2]
  exact ⟨⟨1, μ, ν, inferInstance, inferInstance, hne, hkl⟩,
    ⟨1, μ, ν, inferInstance, inferInstance, hne, hchi⟩⟩

/-- The complete bounds (1.4) on the KL optimal constant. -/
theorem optimalKL_bounds {M : ℝ} (hM : 0 < M) :
    2 * M ^ 2 / (1 - exp (-M ^ 2 / 2)) ≤ optimalKL M ∧
      optimalKL M ≤ 2 * M ^ 2 + 4 := by
  constructor
  · exact le_csSup (klRatioSet_bddAbove hM.le) (sharpness_ratios_mem hM).1
  · apply csSup_le ⟨klExampleRatio M, (sharpness_ratios_mem hM).1⟩
    rintro r ⟨d, μ, ν, hμ, hν, _, rfl⟩
    letI := hμ
    letI := hν
    exact jeffreysRatio_le hM.le μ ν

/-- The complete bounds (1.5) on the chi-square optimal constant. -/
theorem optimalChiSq_bounds {M : ℝ} (hM : 0 < M) :
    (exp (4 * M ^ 2) - 1) / (2 * (1 - exp (-M ^ 2 / 2))) ≤ optimalChiSq M ∧
      optimalChiSq M ≤ 18 * exp (4 * M ^ 2) - 2 := by
  constructor
  · exact le_csSup (chiSqRatioSet_bddAbove hM.le) (sharpness_ratios_mem hM).2
  · apply csSup_le ⟨chiSqExampleRatio M, (sharpness_ratios_mem hM).2⟩
    rintro r ⟨d, μ, ν, hμ, hν, _, rfl⟩
    letI := hμ
    letI := hν
    exact chiSqMaxRatio_le hM.le μ ν

/-- The KL comparison constant differs from its leading term by at most four. -/
theorem optimalKL_error_bounds {M : ℝ} (hM : 0 < M) :
    0 ≤ optimalKL M - 2 * M ^ 2 ∧ optimalKL M - 2 * M ^ 2 ≤ 4 := by
  have hb := optimalKL_bounds hM
  have hden : 0 < 1 - exp (-M ^ 2 / 2) := by
    have := remark1_hellinger_denominator_pos hM
    linarith
  have he : 2 * M ^ 2 ≤ 2 * M ^ 2 / (1 - exp (-M ^ 2 / 2)) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [sq_nonneg M, exp_pos (-M ^ 2 / 2),
      mul_nonneg (sq_nonneg M) (exp_pos (-M ^ 2 / 2)).le]
  constructor <;> linarith

/-- The asymptotic assertion `C_KL(M) = 2 M² + O(1)` as `M → ∞`. -/
theorem optimalKL_asymptotic :
    (fun M : ℝ => optimalKL M - 2 * M ^ 2) =O[atTop] (fun _ => (1 : ℝ)) := by
  apply IsBigO.of_bound 4
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  have hb := optimalKL_error_bounds hM
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1, norm_one, mul_one] using hb.2

/-- The upper and lower chi-square bounds in (1.5) differ by at most a factor
of 36 for every positive radius, not merely asymptotically. -/
theorem chiSq_comparison_factor36 {M : ℝ} (hM : 0 < M) :
    18 * exp (4 * M ^ 2) - 2 ≤ 36 * chiSqExampleRatio M := by
  have hu : exp (-M ^ 2 / 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg M])
  have heu : 1 ≤ exp (4 * M ^ 2) * exp (-M ^ 2 / 2) := by
    rw [← exp_add]
    exact one_le_exp (by nlinarith [sq_nonneg M])
  unfold chiSqExampleRatio
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (remark1_hellinger_denominator_pos hM)).mpr
  nlinarith

/-- Uniform exponential lower and upper envelopes for the optimal chi-square
constant; these make the logarithmic asymptotic statement quantitative. -/
theorem optimalChiSq_exponential_bounds {M : ℝ} (hM : 0 < M) :
    exp (4 * M ^ 2) / 4 ≤ optimalChiSq M ∧
      optimalChiSq M ≤ 18 * exp (4 * M ^ 2) := by
  have hb := optimalChiSq_bounds hM
  have hf := chiSq_comparison_factor36 hM
  have he : 1 ≤ exp (4 * M ^ 2) := one_le_exp (by positivity)
  change _ ≤ 36 * ((exp (4 * M ^ 2) - 1) / (2 * (1 - exp (-M ^ 2 / 2)))) at hf
  constructor <;> nlinarith

/-- The error in `log C_chi²(M) = 4 M² + O(1)` lies between two explicit constants. -/
theorem log_optimalChiSq_error_bounds {M : ℝ} (hM : 0 < M) :
    -log 4 ≤ log (optimalChiSq M) - 4 * M ^ 2 ∧
      log (optimalChiSq M) - 4 * M ^ 2 ≤ log 18 := by
  have hb := optimalChiSq_exponential_bounds hM
  have hp : 0 < optimalChiSq M := lt_of_lt_of_le (by positivity) hb.1
  have hlo := Real.log_le_log (by positivity : 0 < exp (4 * M ^ 2) / 4) hb.1
  have hhi := Real.log_le_log hp hb.2
  rw [log_div (exp_ne_zero _) (by norm_num), log_exp] at hlo
  rw [log_mul (by norm_num) (exp_ne_zero _), log_exp] at hhi
  constructor <;> linarith

/-- The precise Big-O formulation of the logarithmic chi-square asymptotic. -/
theorem optimalChiSq_log_asymptotic :
    (fun M : ℝ => log (optimalChiSq M) - 4 * M ^ 2) =O[atTop]
      (fun _ => (1 : ℝ)) := by
  apply IsBigO.of_bound (log 18)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  have hb := log_optimalChiSq_error_bounds hM
  have hl : log 4 ≤ log 18 := Real.log_le_log (by norm_num) (by norm_num)
  simp only [Real.norm_eq_abs, norm_one, mul_one]
  exact abs_le.mpr ⟨by linarith, hb.2⟩

/-- The leading coefficient 2 in the KL comparison is exact. -/
theorem optimalKL_leading_coefficient :
    Tendsto (fun M : ℝ => optimalKL M / M ^ 2) atTop (𝓝 2) := by
  have hb : ∀ᶠ M : ℝ in atTop, 0 ≤ optimalKL M - 2 * M ^ 2 ∧
      optimalKL M - 2 * M ^ 2 ≤ 4 :=
    (eventually_gt_atTop (0 : ℝ)).mono fun M hM => optimalKL_error_bounds hM
  have he := tendsto_bdd_div_atTop_nhds_zero
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have h := he.add_const 2
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  field_simp
  ring

/-- The coefficient 4 in the exponential growth of the chi-square constant is exact. -/
theorem optimalChiSq_leading_exponent :
    Tendsto (fun M : ℝ => log (optimalChiSq M) / M ^ 2) atTop (𝓝 4) := by
  have hb : ∀ᶠ M : ℝ in atTop, -log 4 ≤ log (optimalChiSq M) - 4 * M ^ 2 ∧
      log (optimalChiSq M) - 4 * M ^ 2 ≤ log 18 :=
    (eventually_gt_atTop (0 : ℝ)).mono fun M hM => log_optimalChiSq_error_bounds hM
  have he := tendsto_bdd_div_atTop_nhds_zero
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have h := he.add_const 4
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  field_simp
  ring

theorem exp_neg_square_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℝ => exp (-c * M ^ 2)) atTop (𝓝 0) := by
  exact tendsto_exp_atBot.comp
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg (neg_neg_of_pos hc))

/-- The lower bound in (1.5) is asymptotic to one half of `exp(4M²)`. -/
theorem chiSqExampleRatio_asymptotic :
    Tendsto (fun M : ℝ => chiSqExampleRatio M / exp (4 * M ^ 2)) atTop (𝓝 (1 / 2)) := by
  have hfour := exp_neg_square_tendsto_zero (by norm_num : (0 : ℝ) < 4)
  have hhalf := exp_neg_square_tendsto_zero (by norm_num : (0 : ℝ) < 1 / 2)
  have hhalf' : Tendsto (fun M : ℝ => exp (-M ^ 2 / 2)) atTop (𝓝 0) := by
    convert! hhalf using 1
    funext M
    congr 1
    ring
  have hn : Tendsto (fun M : ℝ => 1 - exp (-4 * M ^ 2)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hfour
  have hd : Tendsto (fun M : ℝ => 2 * (1 - exp (-M ^ 2 / 2))) atTop (𝓝 (2 * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hhalf')
  have h := hn.div hd (by norm_num : (2 : ℝ) * (1 - 0) ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  have hden : 1 - exp (-M ^ 2 / 2) ≠ 0 := by
    have := remark1_hellinger_denominator_pos hM
    linarith
  unfold chiSqExampleRatio
  simp only [Pi.div_apply, exp_neg]
  field_simp

/-- The ratio of the two displayed bounds in (1.5) tends to 36. -/
theorem chiSq_bounds_ratio_tendsto36 :
    Tendsto (fun M : ℝ => (18 * exp (4 * M ^ 2) - 2) / chiSqExampleRatio M)
      atTop (𝓝 36) := by
  have hf := exp_neg_square_tendsto_zero (by norm_num : (0 : ℝ) < 4)
  have hu : Tendsto (fun M : ℝ => (18 * exp (4 * M ^ 2) - 2) / exp (4 * M ^ 2))
      atTop (𝓝 18) := by
    have h : Tendsto (fun M : ℝ => 18 - 2 * exp (-4 * M ^ 2)) atTop (𝓝 (18 - 2 * 0)) :=
      tendsto_const_nhds.sub (hf.const_mul 2)
    norm_num at h
    apply h.congr'
    filter_upwards [] with M
    simp only [exp_neg]
    field_simp
  have h := hu.div chiSqExampleRatio_asymptotic (by norm_num : (1 / 2 : ℝ) ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [] with M
  exact div_div_div_cancel_right₀ (exp_ne_zero _) _ _

end GaussianMixturePaper
