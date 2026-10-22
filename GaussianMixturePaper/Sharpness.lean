import GaussianComparison.ElementaryTheorem31
import GaussianComparison.ElementaryTheorem32

/-!
# Exact Gaussian calculations used in Remark 1

These results compute divergences for point-mass priors. They do not assert an
asymptotic result for the optimal-constant supremum.
-/

noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace
open GaussianComparison GaussianComparison.GaussianModel

namespace GaussianMixturePaper

variable {d : ℕ} {M : ℝ}

@[simp] theorem mixtureDensity_dirac (a : Ball d M) (x : Space d) :
    mixtureDensity (Measure.dirac a) x = phi (x - a.val) := by
  simp [mixtureDensity]

theorem mixtureDensity_dirac_fun (a : Ball d M) :
    mixtureDensity (Measure.dirac a) = fun x => phi (x - a.val) :=
  funext (mixtureDensity_dirac a)

@[simp] theorem meanScaledDensity_dirac (a : Ball d M) (s : ℝ) (x : Space d) :
    meanScaledDensity (Measure.dirac a) s x = phi (x - s • a.val) := by
  simp [meanScaledDensity]

@[simp] theorem meanScaledPosterior_dirac (a : Ball d M) (s : ℝ) (x : Space d) :
    meanScaledPosterior (Measure.dirac a) s x = a.val := by
  simp only [meanScaledPosterior, posteriorMean, partition, integral_dirac, smul_smul]
  rw [inv_mul_cancel₀ (kernel_pos a.val (s • x) (s ^ 2)).ne', one_smul]

theorem finiteDivergences_shift_pair (hM : 0 ≤ M) (a b : Ball d M) :
    FiniteDivergences volume (fun x => phi (x - a.val)) (fun x => phi (x - b.val)) := by
  simpa only [mixtureDensity_dirac_fun] using
    finiteDivergences_mixture hM (Measure.dirac a) (Measure.dirac b)

/-- Directed KL for arbitrary fixed Gaussian means. -/
theorem kl_shift_pair (hM : 0 ≤ M) (a b : Ball d M) :
    kl volume (fun x => phi (x - a.val)) (fun x => phi (x - b.val)) =
      ‖a.val - b.val‖ ^ 2 / 2 := by
  let F := fun s : ℝ => kl volume (meanScaledDensity (Measure.dirac a) s)
    (meanScaledDensity (Measure.dirac b) s)
  have hd (s : ℝ) : HasDerivAt F (s * ‖a.val - b.val‖ ^ 2) s := by
    have h := meanScalingKL_hasDerivAt hM (Measure.dirac a) (Measure.dirac b) s
    simpa only [F, meanScaledGap, meanScaledPosterior_dirac, meanScaledDensity_dirac,
      integral_mul_const, integral_phi_sub, one_mul] using h
  have hz (s : ℝ) : HasDerivAt (fun t => F t - t ^ 2 * ‖a.val - b.val‖ ^ 2 / 2) 0 s := by
    convert! (hd s).sub ((((hasDerivAt_id s).pow 2).mul_const
      (‖a.val - b.val‖ ^ 2)).div_const 2) using 1
    simp only [id_eq]
    ring
  have he := is_const_of_deriv_eq_zero
    (fun s => (hz s).differentiableAt) (fun s => (hz s).deriv) 1 0
  have hf0 : F 0 = 0 := by simp [F]
  have hf1 : F 1 = kl volume (fun x => phi (x - a.val))
      (fun x => phi (x - b.val)) := by simp [F, mixtureDensity_dirac_fun]
  rw [hf0, hf1] at he
  norm_num at he
  linarith

/-- The ratio of Gaussians with means `a` and `-a`. -/
theorem opposite_gaussian_ratio (a x : Space d) :
    phi (x - a) / phi (x + a) = exp (2 * ⟪a, x⟫_ℝ) := by
  unfold phi
  rw [mul_div_mul_left _ _ (normalizer_pos d).ne', ← exp_sub,
    norm_sub_sq_real, norm_add_sq_real, real_inner_comm x a]
  congr 1
  ring

/-- Completing the square for the chi-square integral. -/
theorem opposite_gaussian_ratio_square (a x : Space d) :
    phi (x - a) ^ 2 / phi (x + a) = exp (4 * ‖a‖ ^ 2) * phi (x - (3 : ℝ) • a) := by
  rw [pow_two, mul_div_assoc, opposite_gaussian_ratio]
  unfold phi
  rw [mul_assoc, ← exp_add]
  rw [show exp (4 * ‖a‖ ^ 2) * (normalizer d * exp (-‖x - (3 : ℝ) • a‖ ^ 2 / 2)) =
    normalizer d * exp (4 * ‖a‖ ^ 2 - ‖x - (3 : ℝ) • a‖ ^ 2 / 2) by
      rw [show 4 * ‖a‖ ^ 2 - ‖x - (3 : ℝ) • a‖ ^ 2 / 2 =
        4 * ‖a‖ ^ 2 + (-‖x - (3 : ℝ) • a‖ ^ 2 / 2) by ring, exp_add]
      ring]
  congr 2
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_right, real_inner_comm a x]
  norm_num
  ring

/-- The square root of the product of two opposite-mean Gaussian densities. -/
theorem opposite_gaussian_affinity_integrand (a x : Space d) :
    sqrt (phi (x - a) * phi (x + a)) = exp (-‖a‖ ^ 2 / 2) * phi x := by
  have he : phi (x - a) * phi (x + a) = (exp (-‖a‖ ^ 2 / 2) * phi x) ^ 2 := by
    unfold phi
    rw [show (normalizer d * exp (-‖x - a‖ ^ 2 / 2)) *
      (normalizer d * exp (-‖x + a‖ ^ 2 / 2)) =
      normalizer d ^ 2 * exp (-‖x - a‖ ^ 2 / 2 - ‖x + a‖ ^ 2 / 2) by
        rw [show -‖x - a‖ ^ 2 / 2 - ‖x + a‖ ^ 2 / 2 =
          (-‖x - a‖ ^ 2 / 2) + (-‖x + a‖ ^ 2 / 2) by ring, exp_add]
        ring]
    rw [show (exp (-‖a‖ ^ 2 / 2) * (normalizer d * exp (-‖x‖ ^ 2 / 2))) ^ 2 =
      normalizer d ^ 2 * exp (-‖a‖ ^ 2 - ‖x‖ ^ 2) by
        calc
          _ = normalizer d ^ 2 *
            ((exp (-‖a‖ ^ 2 / 2) * exp (-‖x‖ ^ 2 / 2)) *
             (exp (-‖a‖ ^ 2 / 2) * exp (-‖x‖ ^ 2 / 2))) := by ring
          _ = normalizer d ^ 2 * exp
            ((-‖a‖ ^ 2 / 2 + -‖x‖ ^ 2 / 2) + (-‖a‖ ^ 2 / 2 + -‖x‖ ^ 2 / 2)) := by
              simp only [exp_add]
          _ = _ := by congr 2; ring]
    congr 2
    rw [norm_sub_sq_real, norm_add_sq_real]
    ring
  rw [he, sqrt_sq_eq_abs, abs_of_pos (mul_pos (exp_pos _) (phi_pos _))]

/-- Exact affinity for the two opposite-mean Gaussians. -/
theorem opposite_gaussian_affinity (a : Space d) :
    affinity volume (fun x => phi (x - a)) (fun x => phi (x + a)) =
      exp (-‖a‖ ^ 2 / 2) := by
  simp only [affinity, opposite_gaussian_affinity_integrand, integral_const_mul,
    integral_phi, mul_one]

/-- Finiteness needed to interpret the opposite-mean integrals as divergences. -/
theorem opposite_gaussian_finite (a : Space d) :
    FiniteDivergences volume (fun x => phi (x - a)) (fun x => phi (x + a)) := by
  have h := finiteDivergences_shift_pair (norm_nonneg a)
    (⟨a, le_rfl⟩ : Ball d ‖a‖) (⟨-a, by simp⟩ : Ball d ‖a‖)
  simpa only [sub_neg_eq_add] using h

theorem opposite_gaussian_hellinger (a : Space d) :
    hellingerSq volume (fun x => phi (x - a)) (fun x => phi (x + a)) =
      2 * (1 - exp (-‖a‖ ^ 2 / 2)) := by
  rw [(opposite_gaussian_finite a).hellingerSq_eq, opposite_gaussian_affinity]

theorem opposite_gaussian_chiSq (a : Space d) :
    chiSq volume (fun x => phi (x - a)) (fun x => phi (x + a)) =
      exp (4 * ‖a‖ ^ 2) - 1 := by
  rw [(opposite_gaussian_finite a).chiSq_eq]
  simp only [opposite_gaussian_ratio_square, integral_const_mul, integral_phi_sub, mul_one]

/-- The Jeffreys divergence of two opposite-mean Gaussians. -/
theorem opposite_gaussian_jeffreys (a : Space d) :
    kl volume (fun x => phi (x - a)) (fun x => phi (x + a)) +
      kl volume (fun x => phi (x + a)) (fun x => phi (x - a)) = 4 * ‖a‖ ^ 2 := by
  let u : Ball d ‖a‖ := ⟨a, le_rfl⟩
  let v : Ball d ‖a‖ := ⟨-a, by simp⟩
  have h₁ := kl_shift_pair (norm_nonneg a) u v
  have h₂ := kl_shift_pair (norm_nonneg a) v u
  have hn : ‖u.val - v.val‖ ^ 2 = 4 * ‖a‖ ^ 2 := by
    change ‖a - -a‖ ^ 2 = _
    rw [sub_neg_eq_add, ← two_smul ℝ a, norm_smul, Real.norm_eq_abs]
    norm_num
    ring
  rw [norm_sub_rev] at h₂
  dsimp [u, v] at h₁ h₂ hn
  simp only [sub_neg_eq_add] at h₁ h₂ hn
  linarith

theorem opposite_gaussian_chiSq_max (a : Space d) :
    max (chiSq volume (fun x => phi (x - a)) (fun x => phi (x + a)))
      (chiSq volume (fun x => phi (x + a)) (fun x => phi (x - a))) =
      exp (4 * ‖a‖ ^ 2) - 1 := by
  have hr := opposite_gaussian_chiSq (-a)
  simp only [sub_neg_eq_add, ← sub_eq_add_neg, norm_neg] at hr
  rw [opposite_gaussian_chiSq, hr, max_self]

/-- The one-dimensional mean vector with coordinate `M`. -/
def sharpnessMean (M : ℝ) : Space 1 := PiLp.single 2 (0 : Fin 1) M

theorem norm_sharpnessMean (hM : 0 ≤ M) : ‖sharpnessMean M‖ = M := by
  simp [sharpnessMean, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg hM]

/-- Exact three formulas in Remark 1, for the one-dimensional pair with means
`M` and `-M`. This also includes the degenerate case `M = 0`. -/
theorem remark1_gaussian_formulas (hM : 0 ≤ M) :
    let p : Space 1 → ℝ := fun x => phi (x - sharpnessMean M)
    let q : Space 1 → ℝ := fun x => phi (x + sharpnessMean M)
    kl volume p q + kl volume q p = 4 * M ^ 2 ∧
    max (chiSq volume p q) (chiSq volume q p) = exp (4 * M ^ 2) - 1 ∧
    hellingerSq volume p q = 2 * (1 - exp (-M ^ 2 / 2)) := by
  dsimp
  rw [opposite_gaussian_jeffreys, opposite_gaussian_chiSq_max,
    opposite_gaussian_hellinger, norm_sharpnessMean hM]
  exact ⟨rfl, rfl, rfl⟩

/-- The ratios in Remark 1 have a strictly positive denominator precisely in
the nondegenerate radius regime used for its lower-bound examples. -/
theorem remark1_hellinger_denominator_pos (hM : 0 < M) :
    0 < 2 * (1 - exp (-M ^ 2 / 2)) := by
  have he : exp (-M ^ 2 / 2) < 1 := by
    apply exp_lt_one_iff.mpr
    nlinarith [sq_pos_of_pos hM]
  linarith

end GaussianMixturePaper
