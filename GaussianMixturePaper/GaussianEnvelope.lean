import GaussianComparison.GaussianModel
import Mathlib.Analysis.Complex.Exponential

/-!
# Exact constants in Lemma 3

The two Gaussian domination inequalities (A.11)--(A.12), including the
dimension-dependent constants. The polynomial estimate uses a split at radius
one instead of expanding the binomial, with the same numerical constant.
-/

noncomputable section
open MeasureTheory Real
open GaussianComparison.GaussianModel

namespace GaussianMixturePaper

/-- Equation (A.13), the single-term bound in the exponential series. -/
theorem radius_pow_le_factorial_exp {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    r ^ k ≤ (k.factorial : ℝ) * exp r := by
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp r hr k)
  simpa [mul_comm] using h

/-- Equation (A.14), with exactly the factor `2^k k!`. -/
theorem one_add_radius_pow_le {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    (1 + r) ^ k ≤ (2 : ℝ) ^ k * (k.factorial : ℝ) * exp r := by
  have hf : (1 : ℝ) ≤ k.factorial := by
    exact_mod_cast (Nat.factorial_pos k)
  have he : (1 : ℝ) ≤ exp r := Real.one_le_exp_iff.mpr hr
  by_cases h : r ≤ 1
  · have hp : (1 + r) ^ k ≤ (2 : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    have hfe : (1 : ℝ) ≤ (k.factorial : ℝ) * exp r := by nlinarith
    exact hp.trans (by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k])
  · have hp : (1 + r) ^ k ≤ (2 * r) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc
      (1 + r) ^ k ≤ (2 * r) ^ k := hp
      _ = (2 : ℝ) ^ k * r ^ k := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ k * ((k.factorial : ℝ) * exp r) :=
        mul_le_mul_of_nonneg_left (radius_pow_le_factorial_exp hr k) (by positivity)
      _ = _ := by ring

private theorem normalizer_mul_wide_gaussian (d : ℕ) :
    normalizer d * (4 * Real.pi) ^ ((d : ℝ) / 2) =
      (2 : ℝ) ^ ((d : ℝ) / 2) := by
  have hm : (4 * Real.pi) ^ ((d : ℝ) / 2) =
      (2 : ℝ) ^ ((d : ℝ) / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) := by
    rw [show (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) by ring]
    exact Real.mul_rpow (by norm_num) (by positivity)
  rw [normalizer, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi), hm]
  have hne : (2 * Real.pi) ^ ((d : ℝ) / 2) ≠ 0 := by positivity
  field_simp

/-- Completing the square in the radial exponent. -/
theorem gaussian_linear_envelope {d : ℕ} (c : ℝ) (x : Space d) :
    phi x * exp (c * ‖x‖) ≤
      (normalizer d * exp (c ^ 2)) * exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) := by
  calc
    phi x * exp (c * ‖x‖) =
        normalizer d * exp (-‖x‖ ^ 2 / 2 + c * ‖x‖) := by
      rw [phi, mul_assoc, ← Real.exp_add]
    _ ≤ normalizer d * exp (c ^ 2 - (1 / 4 : ℝ) * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (normalizer_pos d).le
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (‖x‖ / 2 - c)]
    _ = _ := by
      rw [show c ^ 2 - (1 / 4 : ℝ) * ‖x‖ ^ 2 =
        c ^ 2 + (-(1 / 4 : ℝ) * ‖x‖ ^ 2) by ring, Real.exp_add]
      ring

/-- Lemma 3, equation (A.12). In fact the bound holds for every real `c`. -/
theorem lemma3_exponential (d : ℕ) (c : ℝ) :
    (∫ x : Space d, phi x * exp (c * ‖x‖)) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * exp (c ^ 2) := by
  have hi := (integrable_exp_neg_mul_norm_sq d (b := (1 / 4 : ℝ))
    (by norm_num)).const_mul (normalizer d * exp (c ^ 2))
  calc
    (∫ x : Space d, phi x * exp (c * ‖x‖)) ≤
        ∫ x : Space d,
          (normalizer d * exp (c ^ 2)) * exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) :=
      integral_mono (integrable_phi_mul_exp_norm d c) hi (gaussian_linear_envelope c)
    _ = (normalizer d * exp (c ^ 2)) * (4 * Real.pi) ^ ((d : ℝ) / 2) := by
      rw [integral_const_mul,
        GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : (0 : ℝ) < 1 / 4)]
      congr 1
      simp [Space, div_eq_mul_inv, mul_comm]
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * exp (c ^ 2) := by
      calc
        _ = (normalizer d * (4 * Real.pi) ^ ((d : ℝ) / 2)) * exp (c ^ 2) := by ring
        _ = _ := by rw [normalizer_mul_wide_gaussian]

/-- A pointwise envelope for the polynomial-exponential Gaussian integrand. -/
theorem gaussian_polynomial_envelope {d : ℕ} (c : ℝ) (k : ℕ) (x : Space d) :
    phi x * (1 + ‖x‖) ^ k * exp (c * ‖x‖) ≤
      ((2 : ℝ) ^ k * (k.factorial : ℝ)) * (phi x * exp ((c + 1) * ‖x‖)) := by
  have h := mul_le_mul_of_nonneg_left (one_add_radius_pow_le (norm_nonneg x) k)
    (phi_pos x).le
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (c * ‖x‖)).le
  calc
    _ ≤ phi x * ((2 : ℝ) ^ k * (k.factorial : ℝ) * exp ‖x‖) * exp (c * ‖x‖) := h'
    _ = _ := by
      rw [show (c + 1) * ‖x‖ = ‖x‖ + c * ‖x‖ by ring, Real.exp_add]
      ring

/-- Absolute integrability accompanying Lemma 3. -/
theorem integrable_gaussian_polynomial_exponential (d : ℕ) (c : ℝ) (k : ℕ) :
    Integrable (fun x : Space d => phi x * (1 + ‖x‖) ^ k * exp (c * ‖x‖)) := by
  have hc : Continuous (fun x : Space d => phi x * (1 + ‖x‖) ^ k * exp (c * ‖x‖)) := by
    unfold phi
    fun_prop
  apply ((integrable_phi_mul_exp_norm d (c + 1)).const_mul
    ((2 : ℝ) ^ k * (k.factorial : ℝ))).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hφ := (phi_pos x).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ phi x * (1 + ‖x‖) ^ k * exp (c * ‖x‖))]
  exact gaussian_polynomial_envelope c k x

/-- Lemma 3, equation (A.11), with the exact displayed numerical constant. -/
theorem lemma3_polynomial (d : ℕ) (c : ℝ) (k : ℕ) :
    (∫ x : Space d, phi x * (1 + ‖x‖) ^ k * exp (c * ‖x‖)) ≤
      (2 : ℝ) ^ ((k : ℝ) + (d : ℝ) / 2) * (k.factorial : ℝ) * exp ((c + 1) ^ 2) := by
  calc
    (∫ x : Space d, phi x * (1 + ‖x‖) ^ k * exp (c * ‖x‖)) ≤
        ∫ x : Space d,
          ((2 : ℝ) ^ k * (k.factorial : ℝ)) * (phi x * exp ((c + 1) * ‖x‖)) :=
      integral_mono (integrable_gaussian_polynomial_exponential d c k)
        ((integrable_phi_mul_exp_norm d (c + 1)).const_mul _) (gaussian_polynomial_envelope c k)
    _ = ((2 : ℝ) ^ k * (k.factorial : ℝ)) *
        (∫ x : Space d, phi x * exp ((c + 1) * ‖x‖)) := integral_const_mul _ _
    _ ≤ ((2 : ℝ) ^ k * (k.factorial : ℝ)) *
        ((2 : ℝ) ^ ((d : ℝ) / 2) * exp ((c + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left (lemma3_exponential d (c + 1)) (by positivity)
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      ring

end GaussianMixturePaper
