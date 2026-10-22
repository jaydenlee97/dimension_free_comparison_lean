import GaussianComparison.ElementaryKLCore
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Pointwise algebra and the integrating-factor step of the elementary
chi-square comparison. All analytic hypotheses of the scalar lemma are
explicit; the Gaussian modules discharge them for the actual divergences. -/
noncomputable section
open Real Set
namespace GaussianComparison.ElementaryChi

def modifiedIntegrand (p q : ℝ) : ℝ := p ^ 2 / q - 4 * sqrt (p * q) + 3 * q

theorem polynomial_factorization (z : ℝ) :
    z ^ 4 - 4 * z + 3 = (z - 1) ^ 2 * (z ^ 2 + 2 * z + 3) := by ring

theorem density_mul_sqrt_ratio {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    q * sqrt (p / q) = sqrt (p * q) := by
  rw [sqrt_div hp, sqrt_mul hp]
  have hb : sqrt q ≠ 0 := (sqrt_pos.mpr hq).ne'
  field_simp [hb]
  nlinarith [congrArg (fun t : ℝ => sqrt p * t) (sq_sqrt hq.le)]

/-- The nonnegative polynomial that makes the weighted gap estimate valid. -/
theorem modifiedIntegrand_factorization {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    modifiedIntegrand p q =
      q * (sqrt (p / q) - 1) ^ 2 * ((sqrt (p / q)) ^ 2 + 2 * sqrt (p / q) + 3) := by
  have hz := sq_sqrt (div_nonneg hp hq.le)
  have hz4 : q * (sqrt (p / q)) ^ 4 = p ^ 2 / q := by
    rw [show (sqrt (p / q)) ^ 4 = ((sqrt (p / q)) ^ 2) ^ 2 by ring, hz]
    field_simp [hq.ne']
  rw [mul_assoc, ← polynomial_factorization]
  unfold modifiedIntegrand
  rw [mul_add, mul_sub, hz4]
  have ha := density_mul_sqrt_ratio hp hq
  nlinarith

theorem modifiedIntegrand_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ modifiedIntegrand p q := by
  rw [modifiedIntegrand_factorization hp hq]
  positivity

/-- The negative denominator-weighted term may be dropped only after the
remaining weight has been proved nonnegative. -/
theorem density_weight_bound {p q w B : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (hw0 : 0 ≤ w) (hw : w ≤ B) :
    (2 * (p ^ 2 / q) + sqrt (p * q)) * w ≤
      2 * B * modifiedIntegrand p q + 9 * (sqrt (p * q) * w) := by
  have hh := modifiedIntegrand_nonneg hp hq
  have hm := mul_le_mul_of_nonneg_right hw hh
  have hn := mul_nonneg hq.le hw0
  unfold modifiedIntegrand at *
  nlinarith

/-- Ordinary one-variable calculus, using monotonicity rather than an assumed
fundamental-theorem-of-calculus interchange. -/
theorem comparison_of_derivative_bound (B : ℝ) (hB : 0 ≤ B)
    (G D G' D' : ℝ → ℝ)
    (hG : ContinuousOn G (Icc 0 1)) (hD : ContinuousOn D (Icc 0 1))
    (hGder : ∀ s ∈ Ioo 0 1, HasDerivAt G (G' s) s)
    (hDder : ∀ s ∈ Ioo 0 1, HasDerivAt D (D' s) s)
    (hDnonneg : ∀ s ∈ Ioo 0 1, 0 ≤ D' s)
    (hbound : ∀ s ∈ Ioo 0 1, G' s ≤ 2 * B * s * G s + 18 * D' s)
    (hGzero : G 0 = 0) (hDzero : D 0 = 0) :
    G 1 ≤ 18 * exp B * D 1 := by
  let F : ℝ → ℝ := fun s => exp (-B * s ^ 2) * G s - 18 * D s
  have hE : Continuous (fun s : ℝ => exp (-B * s ^ 2)) := by fun_prop
  have hFcont : ContinuousOn F (Icc 0 1) :=
    (hE.continuousOn.mul hG).sub (hD.const_mul 18)
  have hFder (s : ℝ) (hs : s ∈ Ioo 0 1) :
      HasDerivAt F
        (exp (-B * s ^ 2) * (G' s - 2 * B * s * G s) - 18 * D' s) s := by
    convert! (((((hasDerivAt_id s).pow 2).const_mul (-B)).exp).mul
      (hGder s hs)).sub ((hDder s hs).const_mul 18) using 1
    dsimp [F]
    ring
  have hanti : AntitoneOn F (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hFcont
    · intro s hs
      rw [interior_Icc] at hs
      exact (hFder s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hFder s hs).deriv]
      have he : exp (-B * s ^ 2) ≤ 1 :=
        exp_le_one_iff.mpr (by nlinarith [mul_nonneg hB (sq_nonneg s)])
      have hm := mul_le_mul_of_nonneg_left (hbound s hs) (exp_pos (-B * s ^ 2)).le
      have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr he) (hDnonneg s hs)
      nlinarith
  have hend := hanti (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [F] at hend
  simp only [hGzero, hDzero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    exp_zero, sub_zero, one_pow, mul_one] at hend
  have he : exp B * exp (-B) = 1 := by rw [← exp_add]; simp
  calc
    G 1 = exp B * (exp (-B) * G 1) := by rw [← mul_assoc, he, one_mul]
    _ ≤ exp B * (18 * D 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hend]) (exp_pos B).le
    _ = _ := by ring

end GaussianComparison.ElementaryChi
