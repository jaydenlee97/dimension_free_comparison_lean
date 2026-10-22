import GaussianMixturePaper.AmbientPrior
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Gaussian convolution is injective, and squared Hellinger distance separates
compactly supported priors. The Fourier multiplier of the Gaussian is proved
nonzero; no identifiability hypothesis is used. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology InnerProductSpace
open GaussianComparison GaussianComparison.GaussianModel

namespace GaussianMixturePaper
variable {d : ℕ} {M : ℝ}

def gaussianChar (t : Space d) : ℂ :=
  ∫ x : Space d, (phi x : ℂ) * Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I)

theorem gaussianChar_ne_zero (t : Space d) : gaussianChar t ≠ 0 := by
  have he : gaussianChar t = (normalizer d : ℂ) *
      ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ ((Module.finrank ℝ (Space d) : ℂ) / 2) *
      Complex.exp (Complex.I ^ 2 * (‖t‖ : ℂ) ^ 2 / (4 * (1 / 2 : ℂ))) := by
    unfold gaussianChar
    have hp (x : Space d) :
        (phi x : ℂ) * Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I) =
          (normalizer d : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 +
            Complex.I * (⟪t, x⟫_ℝ : ℂ)) := by
      unfold phi
      push_cast
      rw [mul_assoc, ← Complex.exp_add, real_inner_comm x t]
      congr 2
      ring
    simp_rw [hp]
    rw [integral_const_mul,
      GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by norm_num : 0 < (1 / 2 : ℂ).re)]
    ring
  rw [he]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact_mod_cast (normalizer_pos d).ne'
    · apply Complex.cpow_ne_zero_iff.mpr
      left
      exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by norm_num)
  · exact Complex.exp_ne_zero _

private theorem char_norm (x t : Space d) :
    ‖Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I)‖ = 1 := by
  simp [Complex.norm_exp]

theorem gaussianChar_shift (a t : Space d) :
    (∫ x : Space d, (phi (x - a) : ℂ) * Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I)) =
      gaussianChar t * Complex.exp ((⟪a, t⟫_ℝ : ℂ) * Complex.I) := by
  have he := integral_sub_right_eq_self (μ := (volume : Measure (Space d)))
    (fun x : Space d => (phi x : ℂ) * Complex.exp ((⟪x + a, t⟫_ℝ : ℂ) * Complex.I)) a
  simp only [sub_add_cancel] at he
  rw [he]
  simp only [inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  rfl

/-- Fourier transform of the actual mixture integral. -/
theorem mixture_char_factorization
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (t : Space d) :
    (∫ x : Space d, (mixtureDensity μ x : ℂ) *
      Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I)) =
      gaussianChar t * charFun (μ.map (fun θ : Ball d M => θ.val)) t := by
  have hmeas : AEStronglyMeasurable
      (fun p : Space d × Ball d M => (phi (p.1 - p.2.val) : ℂ) *
        Complex.exp ((⟪p.1, t⟫_ℝ : ℂ) * Complex.I)) (volume.prod μ) := by
    exact (by unfold phi; fun_prop : Continuous _).aestronglyMeasurable
  have hi : Integrable
      (fun p : Space d × Ball d M => (phi (p.1 - p.2.val) : ℂ) *
        Complex.exp ((⟪p.1, t⟫_ℝ : ℂ) * Complex.I)) (volume.prod μ) := by
    apply (integrable_mixture_kernel μ).mono' hmeas
    filter_upwards [] with p
    rw [norm_mul, char_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (phi_pos _)]
  calc
    _ = ∫ x : Space d, ∫ θ : Ball d M, (phi (x - θ.val) : ℂ) *
        Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I) ∂μ := by
      congr 1
      funext x
      rw [integral_mul_const, integral_complex_ofReal]
      rfl
    _ = ∫ θ : Ball d M, (∫ x : Space d, (phi (x - θ.val) : ℂ) *
        Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I)) ∂μ := integral_integral_swap hi
    _ = gaussianChar t * ∫ θ : Ball d M,
        Complex.exp ((⟪θ.val, t⟫_ℝ : ℂ) * Complex.I) ∂μ := by
      simp_rw [gaussianChar_shift]
      rw [integral_const_mul]
    _ = _ := by
      congr 1
      unfold charFun
      exact (integral_map
        (show AEMeasurable (fun θ : Ball d M => θ.val) μ from measurable_subtype_coe.aemeasurable)
        (by fun_prop : AEStronglyMeasurable (fun x : Space d =>
          Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I)) (μ.map (fun θ : Ball d M => θ.val)))).symm


/-- Equality almost everywhere of Gaussian convolution densities determines the prior. -/
theorem mixtureDensity_injective_ae
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (he : mixtureDensity μ =ᵐ[volume] mixtureDensity ν) : μ = ν := by
  have hm : μ.map (fun θ : Ball d M => θ.val) = ν.map (fun θ : Ball d M => θ.val) := by
    letI : IsProbabilityMeasure (μ.map (Subtype.val : Ball d M → Space d)) :=
      Measure.isProbabilityMeasure_map (μ := μ)
        (show AEMeasurable (fun θ : Ball d M => θ.val) μ from measurable_subtype_coe.aemeasurable)
    letI : IsProbabilityMeasure (ν.map (Subtype.val : Ball d M → Space d)) :=
      Measure.isProbabilityMeasure_map (μ := ν)
        (show AEMeasurable (fun θ : Ball d M => θ.val) ν from measurable_subtype_coe.aemeasurable)
    apply Measure.ext_of_charFun
    funext t
    apply mul_left_cancel₀ (gaussianChar_ne_zero t)
    rw [← mixture_char_factorization μ t, ← mixture_char_factorization ν t]
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  exact (MeasurableEmbedding.subtype_coe (measurableSet_priorBall (d := d) (M := M))).map_injective hm

/-- Hellinger distance is zero exactly when the two priors coincide. -/
theorem hellingerSq_mixture_eq_zero_iff (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) = 0 ↔ μ = ν := by
  constructor
  · intro hh
    have hi := (finiteDivergences_mixture hM μ ν).integrable_hellingerSq
    have hz : (fun x => (sqrt (mixtureDensity μ x) - sqrt (mixtureDensity ν x)) ^ 2) =ᵐ[volume]
        fun _ => 0 := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hh
    apply mixtureDensity_injective_ae μ ν
    filter_upwards [hz] with x hx
    have hs : sqrt (mixtureDensity μ x) = sqrt (mixtureDensity ν x) := by nlinarith
    exact (Real.sqrt_inj (mixtureDensity_pos hM μ x).le (mixtureDensity_pos hM ν x).le).mp hs
  · rintro rfl
    exact hellingerSq_self volume _

theorem hellingerSq_mixture_pos (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hne : μ ≠ ν) : 0 < hellingerSq volume (mixtureDensity μ) (mixtureDensity ν) := by
  exact lt_of_le_of_ne (hellingerSq_nonneg volume _ _)
    (Ne.symm fun h => hne ((hellingerSq_mixture_eq_zero_iff hM μ ν).mp h))

/-- Pointwise equality of densities is already enough for identifiability. -/
theorem mixtureDensity_injective
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (he : mixtureDensity μ = mixtureDensity ν) : μ = ν :=
  mixtureDensity_injective_ae μ ν (Filter.Eventually.of_forall fun x => congrFun he x)

/-- Identifiability for the ambient-space formulation of supported priors. -/
theorem ambientMixtureDensity_injective_ae
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ θ ∂μ, ‖θ‖ ≤ M) (hν : ∀ᵐ θ ∂ν, ‖θ‖ ≤ M)
    (he : ambientMixtureDensity μ =ᵐ[volume] ambientMixtureDensity ν) : μ = ν := by
  letI := ballPrior_isProbabilityMeasure μ hμ
  letI := ballPrior_isProbabilityMeasure ν hν
  have he' : mixtureDensity (ballPrior (M := M) μ) =ᵐ[volume]
      mixtureDensity (ballPrior (M := M) ν) := by
    rw [mixtureDensity_ballPrior μ hμ, mixtureDensity_ballPrior ν hν]
    exact he
  have hprior := mixtureDensity_injective_ae _ _ he'
  have hmap := congrArg (Measure.map (fun θ : Ball d M => θ.val)) hprior
  exact (map_ballPrior μ hμ).symm.trans (hmap.trans (map_ballPrior ν hν))

/-- The squared Hellinger distance separates ambient supported probability priors. -/
theorem hellingerSq_ambient_eq_zero_iff (hM : 0 ≤ M)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ θ ∂μ, ‖θ‖ ≤ M) (hν : ∀ᵐ θ ∂ν, ‖θ‖ ≤ M) :
    hellingerSq volume (ambientMixtureDensity μ) (ambientMixtureDensity ν) = 0 ↔ μ = ν := by
  letI := ballPrior_isProbabilityMeasure μ hμ
  letI := ballPrior_isProbabilityMeasure ν hν
  constructor
  · intro hh
    have hh' : hellingerSq volume (mixtureDensity (ballPrior (M := M) μ))
        (mixtureDensity (ballPrior (M := M) ν)) = 0 := by
      rw [mixtureDensity_ballPrior μ hμ, mixtureDensity_ballPrior ν hν]
      exact hh
    have hprior := (hellingerSq_mixture_eq_zero_iff hM _ _).mp hh'
    have hmap := congrArg (Measure.map (fun θ : Ball d M => θ.val)) hprior
    exact (map_ballPrior μ hμ).symm.trans (hmap.trans (map_ballPrior ν hν))
  · rintro rfl
    exact hellingerSq_self volume _

end GaussianMixturePaper
