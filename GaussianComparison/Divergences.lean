import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Actual finite density divergences

All four quantities below are integrals of the indicated density functions.
They are not arbitrary scalar placeholders. Since the real Bochner integral is
zero when its integrand is not integrable, the intended use is explicitly
restricted by `FiniteDivergences` or the corresponding integrability hypotheses.
These definitions do not pretend to define extended-real divergences for
arbitrary nonintegrable densities.
-/

namespace GaussianComparison
open MeasureTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Directed Kullback--Leibler divergence for an integrable log-density ratio. -/
noncomputable def kl (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, p x * log (p x / q x) ∂μ

/-- Directed Pearson chi-square divergence in its nonnegative-integrand form. -/
noncomputable def chiSq (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, (p x / q x - 1) ^ 2 * q x ∂μ

/-- Squared Hellinger distance, with the manuscript's normalization (no 1/2). -/
noncomputable def hellingerSq (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, (sqrt (p x) - sqrt (q x)) ^ 2 ∂μ

/-- Hellinger affinity. -/
noncomputable def affinity (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, sqrt (p x * q x) ∂μ

/-- Explicit validity conditions for all finite divergence expressions used here.
The Gaussian-mixture construction must prove these conditions; they cannot be
replaced by normalization of arbitrary scalar placeholders. -/
structure FiniteDivergences (μ : Measure Ω) (p q : Ω → ℝ) : Prop where
  integrable_p : Integrable p μ
  integrable_q : Integrable q μ
  positive_p : ∀ᵐ x ∂μ, 0 < p x
  positive_q : ∀ᵐ x ∂μ, 0 < q x
  mass_p : (∫ x, p x ∂μ) = 1
  mass_q : (∫ x, q x ∂μ) = 1
  integrable_kl : Integrable (fun x => p x * log (p x / q x)) μ
  integrable_kl_reverse : Integrable (fun x => q x * log (q x / p x)) μ
  integrable_chiSq : Integrable (fun x => (p x / q x - 1) ^ 2 * q x) μ
  integrable_chiSq_reverse : Integrable (fun x => (q x / p x - 1) ^ 2 * p x) μ
  integrable_affinity : Integrable (fun x => sqrt (p x * q x)) μ

/-- Hellinger nonnegativity needs no normalization. -/
theorem hellingerSq_nonneg (μ : Measure Ω) (p q : Ω → ℝ) :
    0 ≤ hellingerSq μ p q :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem hellingerSq_symm (μ : Measure Ω) (p q : Ω → ℝ) :
    hellingerSq μ p q = hellingerSq μ q p := by
  apply integral_congr_ae
  filter_upwards [] with x
  ring

@[simp] theorem hellingerSq_self (μ : Measure Ω) (p : Ω → ℝ) :
    hellingerSq μ p p = 0 := by
  simp [hellingerSq]

@[simp] theorem kl_self (μ : Measure Ω) (p : Ω → ℝ) : kl μ p p = 0 := by
  simp [kl]

@[simp] theorem chiSq_self (μ : Measure Ω) (p : Ω → ℝ) : chiSq μ p p = 0 := by
  have h : (fun x => (p x / p x - 1) ^ 2 * p x) = fun _ => (0 : ℝ) := by
    funext x
    by_cases hx : p x = 0
    · simp [hx]
    · simp [hx]
  simp only [chiSq, h, integral_zero]

theorem chiSq_nonneg (μ : Measure Ω) (p q : Ω → ℝ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ q x) : 0 ≤ chiSq μ p q := by
  apply integral_nonneg_of_ae
  filter_upwards [hq] with x hx
  exact mul_nonneg (sq_nonneg _) hx

theorem affinity_nonneg (μ : Measure Ω) (p q : Ω → ℝ) :
    0 ≤ affinity μ p q :=
  integral_nonneg (fun _ => sqrt_nonneg _)

theorem affinity_symm (μ : Measure Ω) (p q : Ω → ℝ) :
    affinity μ p q = affinity μ q p := by
  simp only [affinity, mul_comm]

/-- Pointwise density algebra behind the affinity identity. -/
theorem hellinger_integrand_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (sqrt p - sqrt q) ^ 2 = p + q - 2 * sqrt (p * q) := by
  rw [sqrt_mul hp]
  nlinarith [sq_sqrt hp, sq_sqrt hq]

/-- Affinity identity with all linearity-of-integral hypotheses explicit. -/
theorem hellingerSq_eq_masses_sub_affinity (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (ha : Integrable (fun x => sqrt (p x * q x)) μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x) :
    hellingerSq μ p q = (∫ x, p x ∂μ) + (∫ x, q x ∂μ) - 2 * affinity μ p q := by
  have he : (fun x => (sqrt (p x) - sqrt (q x)) ^ 2) =ᵐ[μ]
      (fun x => p x + q x - 2 * sqrt (p x * q x)) := by
    filter_upwards [hp0, hq0] with x hpx hqx
    exact hellinger_integrand_eq hpx hqx
  rw [hellingerSq, integral_congr_ae he]
  have hsub := integral_sub (hp.add hq) (ha.const_mul 2)
  simp only [Pi.add_apply] at hsub
  rw [hsub, integral_add hp hq, integral_const_mul]
  rfl

/-- Integrability of the Hellinger integrand follows from density and affinity
integrability and does not have to be inserted as an extra field. -/
theorem FiniteDivergences.integrable_hellingerSq {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) :
    Integrable (fun x => (sqrt (p x) - sqrt (q x)) ^ 2) μ := by
  have hi := (h.integrable_p.add h.integrable_q).sub (h.integrable_affinity.const_mul 2)
  apply hi.congr
  filter_upwards [h.positive_p, h.positive_q] with x hpx hqx
  exact (hellinger_integrand_eq hpx.le hqx.le).symm

theorem FiniteDivergences.hellingerSq_eq {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) : hellingerSq μ p q = 2 * (1 - affinity μ p q) := by
  rw [hellingerSq_eq_masses_sub_affinity μ p q h.integrable_p h.integrable_q
    h.integrable_affinity (h.positive_p.mono fun _ hx => hx.le)
    (h.positive_q.mono fun _ hx => hx.le), h.mass_p, h.mass_q]
  ring

theorem FiniteDivergences.affinity_le_one {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) : affinity μ p q ≤ 1 := by
  have hh := hellingerSq_nonneg μ p q
  rw [h.hellingerSq_eq] at hh
  linarith

theorem FiniteDivergences.hellingerSq_le_two {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) : hellingerSq μ p q ≤ 2 := by
  rw [h.hellingerSq_eq]
  have ha := affinity_nonneg μ p q
  linarith

/-- Swapping the densities preserves every finite-divergence validity condition. -/
theorem FiniteDivergences.symm {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) : FiniteDivergences μ q p where
  integrable_p := h.integrable_q
  integrable_q := h.integrable_p
  positive_p := h.positive_q
  positive_q := h.positive_p
  mass_p := h.mass_q
  mass_q := h.mass_p
  integrable_kl := h.integrable_kl_reverse
  integrable_kl_reverse := h.integrable_kl
  integrable_chiSq := h.integrable_chiSq_reverse
  integrable_chiSq_reverse := h.integrable_chiSq
  integrable_affinity := by simpa only [mul_comm] using h.integrable_affinity

/-- The pointwise logarithmic inequality proving Gibbs' inequality. -/
theorem density_sub_le_kl_integrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p - q ≤ p * log (p / q) := by
  have hl := log_le_sub_one_of_pos (div_pos hq hp)
  have hm := mul_le_mul_of_nonneg_left hl hp.le
  have he : log (q / p) = -log (p / q) := by
    rw [log_div hq.ne' hp.ne', log_div hp.ne' hq.ne']
    ring
  have hc : p * (q / p - 1) = q - p := by
    field_simp [hp.ne']
  rw [he, hc] at hm
  nlinarith

/-- Gibbs' inequality under explicit positive normalized finite-density hypotheses. -/
theorem kl_nonneg (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐ x ∂μ, 0 < p x) (hq0 : ∀ᵐ x ∂μ, 0 < q x)
    (hp1 : (∫ x, p x ∂μ) = 1) (hq1 : (∫ x, q x ∂μ) = 1)
    (hk : Integrable (fun x => p x * log (p x / q x)) μ) :
    0 ≤ kl μ p q := by
  have hi := integral_mono_ae (hp.sub hq) hk (show
      ∀ᵐ x ∂μ, p x - q x ≤ p x * log (p x / q x) from by
        filter_upwards [hp0, hq0] with x hpx hqx
        exact density_sub_le_kl_integrand hpx hqx)
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hp hq, hp1, hq1] at hi
  simpa only [sub_self, kl] using hi

theorem FiniteDivergences.kl_nonneg {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) : 0 ≤ kl μ p q :=
  GaussianComparison.kl_nonneg μ p q h.integrable_p h.integrable_q
    h.positive_p h.positive_q h.mass_p h.mass_q h.integrable_kl

/-- Pointwise algebra for the Jeffreys (symmetrized KL) integrand. -/
theorem symmetrized_kl_integrand {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    p * log (p / q) + q * log (q / p) = (p - q) * log (p / q) := by
  rw [log_div hp hq, log_div hq hp]
  ring

/-- The manuscript's symmetrized-KL integral is the sum of the two actual
oriented KL divergences, with no implicit cancellation of infinite values. -/
theorem kl_add_reverse (μ : Measure Ω) (p q : Ω → ℝ)
    (hp0 : ∀ᵐ x ∂μ, p x ≠ 0) (hq0 : ∀ᵐ x ∂μ, q x ≠ 0)
    (hk : Integrable (fun x => p x * log (p x / q x)) μ)
    (hkr : Integrable (fun x => q x * log (q x / p x)) μ) :
    kl μ p q + kl μ q p = ∫ x, (p x - q x) * log (p x / q x) ∂μ := by
  rw [kl, kl, ← integral_add hk hkr]
  apply integral_congr_ae
  filter_upwards [hp0, hq0] with x hpx hqx
  exact symmetrized_kl_integrand hpx hqx

/-- Pointwise chi-square algebra; the denominator must be nonzero. -/
theorem chiSq_integrand_eq {p q : ℝ} (hq : q ≠ 0) :
    (p / q - 1) ^ 2 * q = p ^ 2 / q - 2 * p + q := by
  field_simp [hq]
  ring

/-- The second moment of the likelihood ratio is integrable whenever the
chi-square integrand and the two densities are integrable. -/
theorem FiniteDivergences.integrable_ratio_square {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) : Integrable (fun x => p x ^ 2 / q x) μ := by
  have hi := (h.integrable_chiSq.add (h.integrable_p.const_mul 2)).sub h.integrable_q
  apply hi.congr
  filter_upwards [h.positive_q] with x hqx
  have he := chiSq_integrand_eq (p := p x) hqx.ne'
  dsimp
  linarith

/-- Pearson chi-square as the normalized ratio second moment minus one. -/
theorem FiniteDivergences.chiSq_eq {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) :
    chiSq μ p q = (∫ x, p x ^ 2 / q x ∂μ) - 1 := by
  have he : (fun x => (p x / q x - 1) ^ 2 * q x) =ᵐ[μ]
      (fun x => p x ^ 2 / q x - 2 * p x + q x) := by
    filter_upwards [h.positive_q] with x hqx
    exact chiSq_integrand_eq hqx.ne'
  rw [chiSq, integral_congr_ae he]
  have hadd := integral_add (h.integrable_ratio_square.sub (h.integrable_p.const_mul 2))
    h.integrable_q
  simp only [Pi.sub_apply] at hadd
  rw [hadd, integral_sub h.integrable_ratio_square (h.integrable_p.const_mul 2)]
  rw [integral_const_mul, h.mass_p, h.mass_q]
  ring


/-- The scalar terminal half-log likelihood ratio. -/
noncomputable def halfLogRatio (p q : ℝ) : ℝ := log (p / q) / 2

/-- The exponentiated terminal likelihood ratio, for positive densities. -/
theorem exp_twice_halfLogRatio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    exp (2 * halfLogRatio p q) = p / q := by
  unfold halfLogRatio
  rw [show 2 * (log (p / q) / 2) = log (p / q) by ring]
  exact Real.exp_log (div_pos hp hq)

/-- An exponential expression that avoids introducing a new definition of tanh. -/
theorem tanh_eq_exp_twice (y : ℝ) :
    tanh y = (exp (2 * y) - 1) / (exp (2 * y) + 1) := by
  have he : exp (2 * y) = exp y ^ 2 := by rw [two_mul, exp_add, pow_two]
  have hden : exp y + (exp y)⁻¹ ≠ 0 := by positivity
  have hden2 : exp y ^ 2 + 1 ≠ 0 := by positivity
  rw [Real.tanh_eq, exp_neg, he]
  field_simp [Real.exp_ne_zero, hden, hden2]

/-- The exact hyperbolic likelihood-ratio identity used in Theorem 3.1. -/
theorem tanh_halfLogRatio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    tanh (halfLogRatio p q) = (p - q) / (p + q) := by
  rw [tanh_eq_exp_twice, exp_twice_halfLogRatio hp hq]
  have hsum : p + q ≠ 0 := (add_pos hp hq).ne'
  have hratio : p / q + 1 ≠ 0 := by positivity
  field_simp [hq.ne', hsum, hratio]

/-- Reciprocal cosh expressed in the exponential coordinate. -/
theorem one_div_cosh_eq_exp_twice (y : ℝ) :
    1 / cosh y = 2 * exp y / (exp (2 * y) + 1) := by
  have he : exp (2 * y) = exp y ^ 2 := by rw [two_mul, exp_add, pow_two]
  have hden : exp y + (exp y)⁻¹ ≠ 0 := by positivity
  have hden2 : exp y ^ 2 + 1 ≠ 0 := by positivity
  rw [Real.cosh_eq, exp_neg, he]
  field_simp [Real.exp_ne_zero, hden, hden2]

/-- Square-root identification without branch ambiguity. -/
theorem sqrt_mul_eq_exp_halfLogRatio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    sqrt (p * q) = exp (halfLogRatio p q) * q := by
  have he : exp (halfLogRatio p q) ^ 2 = p / q := by
    calc
      exp (halfLogRatio p q) ^ 2 = exp (2 * halfLogRatio p q) := by
        rw [pow_two, ← exp_add, two_mul]
      _ = p / q := exp_twice_halfLogRatio hp hq
  have heq : exp (halfLogRatio p q) ^ 2 * q = p := (eq_div_iff hq.ne').mp he
  apply (sqrt_eq_iff_eq_sq (mul_nonneg hp.le hq.le) (by positivity)).mpr
  calc
    p * q = (exp (halfLogRatio p q) ^ 2 * q) * q := by rw [heq]
    _ = (exp (halfLogRatio p q) * q) ^ 2 := by ring

/-- The exact sech identity used to identify terminal Hellinger affinity. -/
theorem one_div_cosh_halfLogRatio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    1 / cosh (halfLogRatio p q) = 2 * sqrt (p * q) / (p + q) := by
  rw [one_div_cosh_eq_exp_twice, exp_twice_halfLogRatio hp hq,
    sqrt_mul_eq_exp_halfLogRatio hp hq]
  have hsum : p + q ≠ 0 := (add_pos hp hq).ne'
  have hratio : p / q + 1 ≠ 0 := by positivity
  field_simp [hq.ne', hsum, hratio]

/-- Pointwise terminal KL identity under the arithmetic-mean density. -/
theorem terminal_kl_integrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (p - q) * log (p / q) =
      4 * ((p + q) / 2 * (halfLogRatio p q * tanh (halfLogRatio p q))) := by
  rw [tanh_halfLogRatio hp hq, halfLogRatio]
  field_simp [(add_pos hp hq).ne']
  ring

/-- Pointwise terminal Hellinger identity under the arithmetic-mean density. -/
theorem terminal_hellinger_integrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (sqrt p - sqrt q) ^ 2 =
      2 * ((p + q) / 2 * (1 - 1 / cosh (halfLogRatio p q))) := by
  rw [hellinger_integrand_eq hp.le hq.le, one_div_cosh_halfLogRatio hp hq]
  field_simp [(add_pos hp hq).ne']

/-- The terminal KL calculation as an equality of genuine density integrals.
No path process or abstract stochastic expectation is assumed in this theorem. -/
theorem FiniteDivergences.terminal_kl_identity {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) :
    kl μ p q + kl μ q p = 4 * (∫ x,
      (p x + q x) / 2 * (halfLogRatio (p x) (q x) * tanh (halfLogRatio (p x) (q x))) ∂μ) := by
  rw [kl_add_reverse μ p q (h.positive_p.mono fun _ hx => hx.ne')
    (h.positive_q.mono fun _ hx => hx.ne') h.integrable_kl h.integrable_kl_reverse,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [h.positive_p, h.positive_q] with x hpx hqx
  exact terminal_kl_integrand hpx hqx

/-- The terminal Hellinger calculation as an equality of genuine integrals. -/
theorem FiniteDivergences.terminal_hellinger_identity {μ : Measure Ω} {p q : Ω → ℝ}
    (h : FiniteDivergences μ p q) :
    hellingerSq μ p q = 2 * (∫ x,
      (p x + q x) / 2 * (1 - 1 / cosh (halfLogRatio (p x) (q x))) ∂μ) := by
  rw [hellingerSq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [h.positive_p, h.positive_q] with x hpx hqx
  exact terminal_hellinger_integrand hpx hqx


/-- Terminal Hellinger integrand under the denominator density. -/
theorem terminal_hellinger_eta_integrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (sqrt p - sqrt q) ^ 2 = (exp (halfLogRatio p q) - 1) ^ 2 * q := by
  have he : exp (halfLogRatio p q) ^ 2 = p / q := by
    calc
      exp (halfLogRatio p q) ^ 2 = exp (2 * halfLogRatio p q) := by
        rw [pow_two, ← exp_add, two_mul]
      _ = p / q := exp_twice_halfLogRatio hp hq
  have heq := (eq_div_iff hq.ne').mp he
  rw [hellinger_integrand_eq hp.le hq.le, sqrt_mul_eq_exp_halfLogRatio hp hq]
  nlinarith

/-- The likelihood-ratio-square integrand for actual Pearson divergence. -/
theorem terminal_chiSq_integrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (p / q - 1) ^ 2 * q = (exp (2 * halfLogRatio p q) - 1) ^ 2 * q := by
  rw [exp_twice_halfLogRatio hp hq]

/-- Density-level starting identity in the appendix proof of the Hellinger clock
identity. The later expected time-integral identity still requires Itô calculus. -/
theorem FiniteDivergences.terminal_hellinger_eta_identity
    {μ : Measure Ω} {p q : Ω → ℝ} (h : FiniteDivergences μ p q) :
    hellingerSq μ p q = ∫ x, (exp (halfLogRatio (p x) (q x)) - 1) ^ 2 * q x ∂μ := by
  apply integral_congr_ae
  filter_upwards [h.positive_p, h.positive_q] with x hpx hqx
  exact terminal_hellinger_eta_integrand hpx hqx

/-- Density-level starting identity in the appendix proof of the chi-square clock
identity. It introduces no unproved stochastic-process assumption. -/
theorem FiniteDivergences.terminal_chiSq_identity
    {μ : Measure Ω} {p q : Ω → ℝ} (h : FiniteDivergences μ p q) :
    chiSq μ p q = ∫ x, (exp (2 * halfLogRatio (p x) (q x)) - 1) ^ 2 * q x ∂μ := by
  apply integral_congr_ae
  filter_upwards [h.positive_p, h.positive_q] with x hpx hqx
  exact terminal_chiSq_integrand hpx hqx


/-- Affinity integrability follows already from integrability of the densities. -/
theorem integrable_affinity_integrand (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x) :
    Integrable (fun x => sqrt (p x * q x)) μ := by
  apply (hp.add hq).mono_nonneg
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (hp.aestronglyMeasurable.mul hq.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun _ => sqrt_nonneg _)
  filter_upwards [hp0, hq0] with x hpx hqx
  change sqrt (p x * q x) ≤ p x + q x
  have he := hellinger_integrand_eq hpx hqx
  have hs := sq_nonneg (sqrt (p x) - sqrt (q x))
  have hr := sqrt_nonneg (p x * q x)
  nlinarith

/-- A two-sided log bound useful for proving actual KL integrability. -/
theorem abs_kl_integrand_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    |p * log (p / q)| ≤ p ^ 2 / q + p + q := by
  have hlo := density_sub_le_kl_integrand hp hq
  have hup := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hp hq)) hp.le
  have he : p * (p / q - 1) = p ^ 2 / q - p := by ring
  rw [he] at hup
  have hr : 0 ≤ p ^ 2 / q := div_nonneg (sq_nonneg p) hq.le
  apply abs_le.mpr
  constructor <;> linarith

/-- Finite likelihood-ratio second moments imply finite directed KL. -/
theorem integrable_kl_of_ratio_square (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐ x ∂μ, 0 < p x) (hq0 : ∀ᵐ x ∂μ, 0 < q x)
    (hr : Integrable (fun x => p x ^ 2 / q x) μ) :
    Integrable (fun x => p x * log (p x / q x)) μ := by
  have hm : AEMeasurable (fun x => p x * log (p x / q x)) μ :=
    hp.aestronglyMeasurable.aemeasurable.mul
      ((hp.aestronglyMeasurable.aemeasurable.div hq.aestronglyMeasurable.aemeasurable).log)
  apply ((hr.add hp).add hq).mono' hm.aestronglyMeasurable
  filter_upwards [hp0, hq0] with x hpx hqx
  simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_kl_integrand_le hpx hqx

/-- Finite ratio second moments also give the nonnegative Pearson integrand. -/
theorem integrable_chiSq_of_ratio_square (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hq0 : ∀ᵐ x ∂μ, q x ≠ 0)
    (hr : Integrable (fun x => p x ^ 2 / q x) μ) :
    Integrable (fun x => (p x / q x - 1) ^ 2 * q x) μ := by
  apply ((hr.sub (hp.const_mul 2)).add hq).congr
  filter_upwards [hq0] with x hqx
  exact (chiSq_integrand_eq hqx).symm

/-- A convenient noncircular constructor: it suffices to prove normalization,
positivity, and both actual ratio second moments. -/
theorem finiteDivergences_of_ratio_square (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐ x ∂μ, 0 < p x) (hq0 : ∀ᵐ x ∂μ, 0 < q x)
    (hp1 : (∫ x, p x ∂μ) = 1) (hq1 : (∫ x, q x ∂μ) = 1)
    (hr : Integrable (fun x => p x ^ 2 / q x) μ)
    (hrr : Integrable (fun x => q x ^ 2 / p x) μ) : FiniteDivergences μ p q where
  integrable_p := hp
  integrable_q := hq
  positive_p := hp0
  positive_q := hq0
  mass_p := hp1
  mass_q := hq1
  integrable_kl := integrable_kl_of_ratio_square μ p q hp hq hp0 hq0 hr
  integrable_kl_reverse := integrable_kl_of_ratio_square μ q p hq hp hq0 hp0 hrr
  integrable_chiSq := integrable_chiSq_of_ratio_square μ p q hp hq
    (hq0.mono fun _ hx => hx.ne') hr
  integrable_chiSq_reverse := integrable_chiSq_of_ratio_square μ q p hq hp
    (hp0.mono fun _ hx => hx.ne') hrr
  integrable_affinity := integrable_affinity_integrand μ p q hp hq
    (hp0.mono fun _ hx => hx.le) (hq0.mono fun _ hx => hx.le)

end GaussianComparison
