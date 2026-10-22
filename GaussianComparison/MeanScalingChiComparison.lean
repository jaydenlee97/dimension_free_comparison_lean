import GaussianComparison.MeanScalingChiCalculus
import GaussianComparison.ElementaryChiCore

/-! The nonnegative modified divergence C+2D and its integrated differential
inequality. Every use of integral linearity or monotonicity has proved
integrability premises. -/
noncomputable section
open MeasureTheory Real Set
namespace GaussianComparison.GaussianModel

def meanScalingModifiedChi {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  meanScalingChiSq μ ν s + 2 * meanScalingHellinger μ ν s

def meanScalingModifiedChiRate {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  meanScalingChiSqRate μ ν s + 2 * meanScalingHellingerRate μ ν s

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem integrable_meanScalingModifiedChi_integrand (s : ℝ) (hs : |s| ≤ 1) :
    Integrable (fun x => ElementaryChi.modifiedIntegrand
      (meanScaledDensity μ s x) (meanScaledDensity ν s x)) := by
  have hf := finiteDivergences_meanScaled hM μ ν s hs
  exact (hf.integrable_ratio_square.sub (hf.integrable_affinity.const_mul 4)).add
    (hf.integrable_q.const_mul 3)

theorem meanScalingModifiedChi_eq_integral (s : ℝ) (hs : |s| ≤ 1) :
    meanScalingModifiedChi μ ν s = ∫ x, ElementaryChi.modifiedIntegrand
      (meanScaledDensity μ s x) (meanScaledDensity ν s x) := by
  have hf := finiteDivergences_meanScaled hM μ ν s hs
  unfold meanScalingModifiedChi meanScalingChiSq meanScalingHellinger
  rw [hf.chiSq_eq, hf.hellingerSq_eq]
  unfold ElementaryChi.modifiedIntegrand affinity
  have hadd := integral_add (hf.integrable_ratio_square.sub (hf.integrable_affinity.const_mul 4))
    (hf.integrable_q.const_mul 3)
  have hsub := integral_sub hf.integrable_ratio_square (hf.integrable_affinity.const_mul 4)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul, integral_const_mul, hf.mass_q]
  ring

theorem meanScalingModifiedChi_rate_bound (s : ℝ) (hs : s ∈ Icc 0 1) :
    meanScalingModifiedChiRate μ ν s ≤
      8 * M ^ 2 * s * meanScalingModifiedChi μ ν s + 18 * meanScalingHellingerRate μ ν s := by
  have ha : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hf := finiteDivergences_meanScaled hM μ ν s ha
  have hcR : Continuous (fun x => meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x) :=
    ((continuous_meanScaledDensity_space μ s).pow 2).div
      (continuous_meanScaledDensity_space ν s) (fun x => (meanScaledDensity_pos hM ν s x).ne')
  have iR := integrable_mul_meanScaledGap_sq hM μ ν s hf.integrable_ratio_square hcR
  have iA := integrable_meanScalingHellingerRate_integrand hM μ ν s ha
  have iH := integrable_meanScalingModifiedChi_integrand hM μ ν s ha
  have hp : ∀ᵐ x : Space d ∂volume,
      2 * ((meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x) * ‖meanScaledGap μ ν s x‖ ^ 2) +
        sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) * ‖meanScaledGap μ ν s x‖ ^ 2 ≤
      8 * M ^ 2 * ElementaryChi.modifiedIntegrand (meanScaledDensity μ s x) (meanScaledDensity ν s x) +
        9 * (sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) * ‖meanScaledGap μ ν s x‖ ^ 2) := by
    filter_upwards [] with x
    have hb := ElementaryChi.density_weight_bound
      (meanScaledDensity_pos hM μ s x).le (meanScaledDensity_pos hM ν s x)
      (sq_nonneg ‖meanScaledGap μ ν s x‖) (sq_norm_meanScaledGap_le hM μ ν s x)
    nlinarith
  have hi := integral_mono_ae ((iR.const_mul 2).add iA)
    ((iH.const_mul (8 * M ^ 2)).add (iA.const_mul 9)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (iR.const_mul 2) iA,
    integral_add (iH.const_mul (8 * M ^ 2)) (iA.const_mul 9),
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left hi hs.1
  rw [meanScalingModifiedChi_eq_integral hM μ ν s ha]
  unfold meanScalingModifiedChiRate meanScalingChiSqRate meanScalingHellingerRate
  nlinarith

theorem continuousOn_meanScalingModifiedChi :
    ContinuousOn (meanScalingModifiedChi μ ν) (Icc 0 1) :=
  (continuous_meanScalingChiSq hM μ ν).continuousOn.add
    ((continuousOn_meanScalingHellinger hM μ ν).const_mul 2)

theorem meanScalingModifiedChi_hasDerivAt (s : ℝ) (hs : s ∈ Ioo 0 1) :
    HasDerivAt (meanScalingModifiedChi μ ν) (meanScalingModifiedChiRate μ ν s) s :=
  (meanScalingChiSq_hasDerivAt hM μ ν s).add
    ((meanScalingHellinger_hasDerivAt hM μ ν s hs).const_mul 2)

omit hM in
@[simp] theorem meanScalingModifiedChi_zero : meanScalingModifiedChi μ ν 0 = 0 := by
  simp [meanScalingModifiedChi]

/-- Instantiate the integrating-factor lemma with actual Gaussian divergences
and their proved derivatives. No comparison theorem is assumed. -/
theorem meanScaling_chiSq_comparison :
    chiSq volume (mixtureDensity μ) (mixtureDensity ν) ≤
      (18 * exp (4 * M ^ 2) - 2) * hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  have h := ElementaryChi.comparison_of_derivative_bound (4 * M ^ 2) (by positivity)
    (meanScalingModifiedChi μ ν) (meanScalingHellinger μ ν)
    (meanScalingModifiedChiRate μ ν) (meanScalingHellingerRate μ ν)
    (continuousOn_meanScalingModifiedChi hM μ ν) (continuousOn_meanScalingHellinger hM μ ν)
    (meanScalingModifiedChi_hasDerivAt hM μ ν) (meanScalingHellinger_hasDerivAt hM μ ν)
    (fun s hs => meanScalingHellingerRate_nonneg μ ν s hs.1.le)
    (fun s hs => by
      convert! meanScalingModifiedChi_rate_bound hM μ ν s ⟨hs.1.le, hs.2.le⟩ using 1
      ring)
    (meanScalingModifiedChi_zero μ ν) (meanScalingHellinger_zero μ ν)
  dsimp [meanScalingModifiedChi] at h
  rw [meanScalingChiSq_one, meanScalingHellinger_one] at h
  nlinarith

end GaussianComparison.GaussianModel
