import GaussianMixturePaper.DensityRegularity
import GaussianMixturePaper.GaussianEnvelope
import GaussianMixturePaper.AnalyticLemmas
import GaussianMixturePaper.GlobalRegularity

/-!
# The explicit envelopes in Appendix A.3.6

All six functions below have exactly the manuscript's coefficients. Stronger
intermediate derivative estimates are used where this shortens the proof.
-/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology InnerProductSpace
open GaussianComparison GaussianComparison.GaussianModel
namespace GaussianMixturePaper

variable {d : ℕ} {M : ℝ}

/-- P_J in Appendix A.3.6. -/
def PJ (M T : ℝ) (x : Space d) : ℝ :=
  (T ^ 2 * M ^ 2 / 2) * (phi x * exp (T * M * ‖x‖)) +
    (2 * T * M) * (phi x * (1 + ‖x‖) * exp (T * M * ‖x‖))

/-- Q_J in Appendix A.3.6. -/
def QJ (M T : ℝ) (x : Space d) : ℝ :=
  (T * M ^ 2 * (2 + T ^ 2 * M ^ 2 / 2)) * (phi x * exp (T * M * ‖x‖)) +
    (2 * T ^ 2 * M ^ 3 + M * (2 + T ^ 2 * M ^ 2 / 2)) *
      (phi x * (1 + ‖x‖) * exp (T * M * ‖x‖)) +
    (2 * T * M ^ 2) * (phi x * (1 + ‖x‖) ^ 2 * exp (T * M * ‖x‖))

/-- P_C in Appendix A.3.6. -/
def PC (M T : ℝ) (x : Space d) : ℝ :=
  exp (T ^ 2 * M ^ 2 / 2) * (phi x * exp (3 * T * M * ‖x‖))

/-- Q_C in Appendix A.3.6. -/
def QC (M T : ℝ) (x : Space d) : ℝ :=
  (4 * T * M ^ 2 * exp (T ^ 2 * M ^ 2)) * (phi x * exp (5 * T * M * ‖x‖)) +
    (4 * M * exp (T ^ 2 * M ^ 2)) * (phi x * (1 + ‖x‖) * exp (5 * T * M * ‖x‖))

/-- P_A in Appendix A.3.6. -/
def PA (M T : ℝ) (x : Space d) : ℝ := phi x * exp (T * M * ‖x‖)

/-- Q_A in Appendix A.3.6. -/
def QA (M T : ℝ) (x : Space d) : ℝ :=
  (T * M ^ 2 * exp (T ^ 2 * M ^ 2 / 4)) * (phi x * exp (2 * T * M * ‖x‖)) +
    (M * exp (T ^ 2 * M ^ 2 / 4)) * (phi x * (1 + ‖x‖) * exp (2 * T * M * ‖x‖))

theorem appendix_envelopes_integrable (M T : ℝ) :
    Integrable (PJ (d := d) M T) ∧ Integrable (QJ (d := d) M T) ∧
    Integrable (PC (d := d) M T) ∧ Integrable (QC (d := d) M T) ∧
    Integrable (PA (d := d) M T) ∧ Integrable (QA (d := d) M T) := by
  have h0 (c : ℝ) := integrable_phi_mul_exp_norm d c
  have h1 (c : ℝ) : Integrable (fun x : Space d => phi x * (1 + ‖x‖) * exp (c * ‖x‖)) := by
    simpa using integrable_gaussian_polynomial_exponential d c 1
  have h2 (c : ℝ) := integrable_gaussian_polynomial_exponential d c 2
  exact ⟨((h0 _).const_mul _).add ((h1 _).const_mul _),
    (((h0 _).const_mul _).add ((h1 _).const_mul _)).add ((h2 _).const_mul _),
    (h0 _).const_mul _, ((h0 _).const_mul _).add ((h1 _).const_mul _),
    h0 _, ((h0 _).const_mul _).add ((h1 _).const_mul _)⟩

/-- The three unnormalized raw integrands used in the appendix. -/
def rawKL (μ ν : Measure (Ball d M)) (t : ℝ) (x : Space d) : ℝ :=
  meanScaledDensity μ t x * log (meanScaledDensity μ t x / meanScaledDensity ν t x)
def rawChi (μ ν : Measure (Ball d M)) (t : ℝ) (x : Space d) : ℝ :=
  meanScaledDensity μ t x ^ 2 / meanScaledDensity ν t x
def rawAffinity (μ ν : Measure (Ball d M)) (t : ℝ) (x : Space d) : ℝ :=
  sqrt (meanScaledDensity μ t x * meanScaledDensity ν t x)

private theorem abs_kl_rate_le {p q p' q' a b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ha : 0 ≤ a)
    (hp' : |p'| ≤ a * p) (hq' : |q'| ≤ a * q)
    (hb : |log (p / q)| ≤ b) :
    |p' * (1 + log (p / q)) - (p / q) * q'| ≤ a * (2 + b) * p := by
  have hlog : |1 + log (p / q)| ≤ 1 + b := by
    exact (abs_add_le _ _).trans (by simpa using add_le_add_left hb 1)
  have h1 : |p' * (1 + log (p / q))| ≤ (a * p) * (1 + b) := by
    rw [abs_mul]
    exact mul_le_mul hp' hlog (abs_nonneg _) (by positivity)
  have h2 : |(p / q) * q'| ≤ a * p := by
    rw [abs_mul, abs_of_pos (div_pos hp hq)]
    calc
      _ ≤ (p / q) * (a * q) := mul_le_mul_of_nonneg_left hq' (div_pos hp hq).le
      _ = _ := by field_simp
  calc
    _ ≤ |p' * (1 + log (p / q))| + |(p / q) * q'| := abs_sub _ _
    _ ≤ (a * p) * (1 + b) + a * p := add_le_add h1 h2
    _ = _ := by ring

private theorem abs_chi_rate_le {p q p' q' a : ℝ}
    (hp : 0 < p) (hq : 0 < q) (_ha : 0 ≤ a)
    (hp' : |p'| ≤ a * p) (hq' : |q'| ≤ a * q) :
    |2 * p' * (p / q) - q' * (p / q) ^ 2| ≤ 3 * a * (p ^ 2 / q) := by
  have h1 : |2 * p' * (p / q)| ≤ 2 * a * (p ^ 2 / q) := by
    rw [abs_mul, abs_mul, abs_of_pos (div_pos hp hq)]
    norm_num
    calc
      _ ≤ 2 * (a * p) * (p / q) := by gcongr
      _ = _ := by field_simp
  have h2 : |q' * (p / q) ^ 2| ≤ a * (p ^ 2 / q) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (p / q))]
    calc
      _ ≤ (a * q) * (p / q) ^ 2 := mul_le_mul_of_nonneg_right hq' (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ |2 * p' * (p / q)| + |q' * (p / q) ^ 2| := abs_sub _ _
    _ ≤ 2 * a * (p ^ 2 / q) + a * (p ^ 2 / q) := add_le_add h1 h2
    _ = _ := by ring

private theorem abs_affinity_rate_le {p q p' q' a : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ha : 0 ≤ a)
    (hp' : |p'| ≤ a * p) (hq' : |q'| ≤ a * q) :
    |(p' * q + p * q') / (2 * sqrt (p * q))| ≤ a * sqrt (p * q) := by
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * sqrt (p * q))]
  apply (div_le_iff₀ (by positivity : 0 < 2 * sqrt (p * q))).mpr
  have h1 : |p' * q| ≤ a * p * q := by
    rw [abs_mul, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_right hp' hq.le
  have h2 : |p * q'| ≤ p * (a * q) := by
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left hq' hp.le
  have hs := sq_sqrt (mul_pos hp hq).le
  calc
    _ ≤ |p' * q| + |p * q'| := abs_add_le _ _
    _ ≤ a * p * q + p * (a * q) := add_le_add h1 h2
    _ = a * sqrt (p * q) * (2 * sqrt (p * q)) := by nlinarith

variable (hM : 0 ≤ M) (μ ν : Measure (Ball d M))
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem rawKL_deriv (t : ℝ) (x : Space d) :
    deriv (fun s => rawKL μ ν s x) t =
      deriv (fun s => meanScaledDensity μ s x) t *
        (1 + log (meanScaledDensity μ t x / meanScaledDensity ν t x)) -
      (meanScaledDensity μ t x / meanScaledDensity ν t x) *
        deriv (fun s => meanScaledDensity ν s x) t := by
  have hp := (meanScaledDensity_hasDerivAt μ x t).differentiableAt.hasDerivAt
  have hq := (meanScaledDensity_hasDerivAt ν x t).differentiableAt.hasDerivAt
  have hpp := meanScaledDensity_pos hM μ t x
  have hqp := meanScaledDensity_pos hM ν t x
  have hd := hp.mul ((hp.div hq hqp.ne').log (div_pos hpp hqp).ne')
  change HasDerivAt (fun s => rawKL μ ν s x) _ t at hd
  rw [hd.deriv]
  simp only [Pi.div_apply]
  field_simp
  ring

theorem rawChi_deriv (t : ℝ) (x : Space d) :
    deriv (fun s => rawChi μ ν s x) t =
      2 * deriv (fun s => meanScaledDensity μ s x) t *
        (meanScaledDensity μ t x / meanScaledDensity ν t x) -
      deriv (fun s => meanScaledDensity ν s x) t *
        (meanScaledDensity μ t x / meanScaledDensity ν t x) ^ 2 := by
  have hp := (meanScaledDensity_hasDerivAt μ x t).differentiableAt.hasDerivAt
  have hq := (meanScaledDensity_hasDerivAt ν x t).differentiableAt.hasDerivAt
  have hd := (hp.pow 2).div hq (meanScaledDensity_pos hM ν t x).ne'
  change HasDerivAt (fun s => rawChi μ ν s x) _ t at hd
  rw [hd.deriv]
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp

theorem rawAffinity_deriv (t : ℝ) (x : Space d) :
    deriv (fun s => rawAffinity μ ν s x) t =
      (deriv (fun s => meanScaledDensity μ s x) t * meanScaledDensity ν t x +
        meanScaledDensity μ t x * deriv (fun s => meanScaledDensity ν s x) t) /
      (2 * sqrt (meanScaledDensity μ t x * meanScaledDensity ν t x)) := by
  have hp := (meanScaledDensity_hasDerivAt μ x t).differentiableAt.hasDerivAt
  have hq := (meanScaledDensity_hasDerivAt ν x t).differentiableAt.hasDerivAt
  have hd := (hp.mul hq).sqrt (mul_pos (meanScaledDensity_pos hM μ t x)
    (meanScaledDensity_pos hM ν t x)).ne'
  change HasDerivAt (fun s => rawAffinity μ ν s x) _ t at hd
  exact hd.deriv

/-- The log-likelihood ratio in the appendix's original density notation. -/
theorem raw_logRatio_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |log (meanScaledDensity μ t x / meanScaledDensity ν t x)| ≤
      2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2 := by
  have h := logRatio_bound hM μ ν hT ht x
  change |log (scaledRatio μ ν t x)| ≤ _ at h
  rw [← density_ratio_eq_scaledRatio μ ν] at h
  exact h

theorem raw_ratio_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    meanScaledDensity μ t x / meanScaledDensity ν t x ≤
      exp (2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2) := by
  have hp := div_pos (meanScaledDensity_pos hM μ t x) (meanScaledDensity_pos hM ν t x)
  calc
    _ = exp (log (meanScaledDensity μ t x / meanScaledDensity ν t x)) := (exp_log hp).symm
    _ ≤ _ := exp_le_exp.mpr ((le_abs_self _).trans (raw_logRatio_bound hM μ ν hT ht x))

theorem rawKL_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |rawKL μ ν t x| ≤ PJ M T x := by
  have hp := meanScaledDensity_pos hM μ t x
  have hb := raw_logRatio_bound hM μ ν hT ht x
  have hu := (density_envelopes hM μ hT ht x).2
  have hφ := (phi_pos x).le
  unfold rawKL
  rw [abs_mul, abs_of_pos hp]
  calc
    _ ≤ (phi x * exp (T * M * ‖x‖)) * (2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2) :=
      mul_le_mul hu hb (abs_nonneg _) (by positivity)
    _ ≤ PJ M T x := by
      apply le_of_sub_nonneg
      have h : 0 ≤ (2 * T * M) * (phi x * exp (T * M * ‖x‖)) := by positivity
      convert! h using 1
      unfold PJ; ring

theorem rawChi_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |rawChi μ ν t x| ≤ PC M T x := by
  have hp := meanScaledDensity_pos hM μ t x
  have hq := meanScaledDensity_pos hM ν t x
  have hu := (density_envelopes hM μ hT ht x).2
  have hr := raw_ratio_bound hM μ ν hT ht x
  have hφ := (phi_pos x).le
  rw [rawChi, abs_of_pos (div_pos (sq_pos_of_pos hp) hq)]
  calc
    _ = meanScaledDensity μ t x * (meanScaledDensity μ t x / meanScaledDensity ν t x) := by ring
    _ ≤ (phi x * exp (T * M * ‖x‖)) * exp (2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2) :=
      mul_le_mul hu hr (div_pos hp hq).le (by positivity)
    _ = PC M T x := by
      unfold PC
      rw [exp_add]
      rw [show 3 * T * M * ‖x‖ = T * M * ‖x‖ + 2 * T * M * ‖x‖ by ring, exp_add]
      ring

theorem rawAffinity_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |rawAffinity μ ν t x| ≤ PA M T x := by
  have hp := meanScaledDensity_pos hM μ t x
  have hq := meanScaledDensity_pos hM ν t x
  have hu := (density_envelopes hM μ hT ht x).2
  have hv := (density_envelopes hM ν hT ht x).2
  have hφ := (phi_pos x).le
  rw [rawAffinity, abs_of_nonneg (sqrt_nonneg _)]
  apply (sqrt_le_left (by unfold PA; positivity)).mpr
  simpa only [PA, pow_two] using mul_le_mul hu hv hq.le (by positivity)

theorem rawKL_deriv_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |deriv (fun s => rawKL μ ν s x) t| ≤ QJ M T x := by
  have hφ := (phi_pos x).le
  have ha : 0 ≤ densityTimeEnvelope M T x := by unfold densityTimeEnvelope; positivity
  have hb : 0 ≤ 2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2 := by positivity
  rw [rawKL_deriv hM μ ν]
  calc
    _ ≤ densityTimeEnvelope M T x * (2 + (2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2)) *
        meanScaledDensity μ t x :=
      abs_kl_rate_le (meanScaledDensity_pos hM μ t x) (meanScaledDensity_pos hM ν t x) ha
        (density_deriv_time_bound hM μ hT ht x) (density_deriv_time_bound hM ν hT ht x)
        (raw_logRatio_bound hM μ ν hT ht x)
    _ ≤ densityTimeEnvelope M T x * (2 + (2 * T * M * ‖x‖ + T ^ 2 * M ^ 2 / 2)) *
        (phi x * exp (T * M * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (density_envelopes hM μ hT ht x).2 (by positivity)
    _ ≤ QJ M T x := by
      apply le_of_sub_nonneg
      have h : 0 ≤ ((2 * T ^ 2 * M ^ 3 + M * (2 + T ^ 2 * M ^ 2 / 2)) +
          2 * T * M ^ 2 * (1 + 2 * ‖x‖)) * (phi x * exp (T * M * ‖x‖)) := by positivity
      convert! h using 1
      unfold QJ densityTimeEnvelope; ring

private theorem PC_le_wide {T : ℝ} (hT : 0 ≤ T) (x : Space d) :
    PC M T x ≤ exp (T ^ 2 * M ^ 2) * (phi x * exp (5 * T * M * ‖x‖)) := by
  have hφ := (phi_pos x).le
  have he : T ^ 2 * M ^ 2 / 2 + 3 * T * M * ‖x‖ ≤
      T ^ 2 * M ^ 2 + 5 * T * M * ‖x‖ := by
    have h1 : 0 ≤ T * M * ‖x‖ := by positivity
    have h2 : 0 ≤ T ^ 2 * M ^ 2 := by positivity
    nlinarith
  calc
    _ = phi x * exp (T ^ 2 * M ^ 2 / 2 + 3 * T * M * ‖x‖) := by unfold PC; rw [exp_add]; ring
    _ ≤ phi x * exp (T ^ 2 * M ^ 2 + 5 * T * M * ‖x‖) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) hφ
    _ = _ := by rw [exp_add]; ring

private theorem PA_le_wide {T : ℝ} (hT : 0 ≤ T) (x : Space d) :
    PA M T x ≤ exp (T ^ 2 * M ^ 2 / 4) * (phi x * exp (2 * T * M * ‖x‖)) := by
  have hφ := (phi_pos x).le
  have he : T * M * ‖x‖ ≤ T ^ 2 * M ^ 2 / 4 + 2 * T * M * ‖x‖ := by
    have h1 : 0 ≤ T * M * ‖x‖ := by positivity
    have h2 : 0 ≤ T ^ 2 * M ^ 2 := by positivity
    nlinarith
  calc
    _ ≤ phi x * exp (T ^ 2 * M ^ 2 / 4 + 2 * T * M * ‖x‖) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) hφ
    _ = _ := by rw [exp_add]; ring

theorem rawChi_deriv_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |deriv (fun s => rawChi μ ν s x) t| ≤ QC M T x := by
  have hφ := (phi_pos x).le
  have ha : 0 ≤ densityTimeEnvelope M T x := by unfold densityTimeEnvelope; positivity
  rw [rawChi_deriv hM μ ν]
  calc
    _ ≤ 3 * densityTimeEnvelope M T x * rawChi μ ν t x :=
      abs_chi_rate_le (meanScaledDensity_pos hM μ t x) (meanScaledDensity_pos hM ν t x) ha
        (density_deriv_time_bound hM μ hT ht x) (density_deriv_time_bound hM ν hT ht x)
    _ ≤ 3 * densityTimeEnvelope M T x * PC M T x :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (rawChi_bound hM μ ν hT ht x)) (by positivity)
    _ ≤ 3 * densityTimeEnvelope M T x *
        (exp (T ^ 2 * M ^ 2) * (phi x * exp (5 * T * M * ‖x‖))) :=
      mul_le_mul_of_nonneg_left (PC_le_wide hM hT x) (by positivity)
    _ ≤ QC M T x := by
      apply le_of_sub_nonneg
      have h : 0 ≤ (densityTimeEnvelope M T x + 4 * M) *
          (exp (T ^ 2 * M ^ 2) * (phi x * exp (5 * T * M * ‖x‖))) := by positivity
      convert! h using 1
      unfold QC densityTimeEnvelope
      ring

theorem rawAffinity_deriv_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |deriv (fun s => rawAffinity μ ν s x) t| ≤ QA M T x := by
  have hφ := (phi_pos x).le
  have ha : 0 ≤ densityTimeEnvelope M T x := by unfold densityTimeEnvelope; positivity
  rw [rawAffinity_deriv hM μ ν]
  calc
    _ ≤ densityTimeEnvelope M T x * rawAffinity μ ν t x :=
      abs_affinity_rate_le (meanScaledDensity_pos hM μ t x) (meanScaledDensity_pos hM ν t x) ha
        (density_deriv_time_bound hM μ hT ht x) (density_deriv_time_bound hM ν hT ht x)
    _ ≤ densityTimeEnvelope M T x * PA M T x :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (rawAffinity_bound hM μ ν hT ht x)) ha
    _ ≤ densityTimeEnvelope M T x *
        (exp (T ^ 2 * M ^ 2 / 4) * (phi x * exp (2 * T * M * ‖x‖))) :=
      mul_le_mul_of_nonneg_left (PA_le_wide hM hT x) ha
    _ ≤ QA M T x := by
      apply le_of_sub_nonneg
      have h : 0 ≤ M * (exp (T ^ 2 * M ^ 2 / 4) * (phi x * exp (2 * T * M * ‖x‖))) := by positivity
      convert! h using 1
      unfold QA densityTimeEnvelope
      ring

/-- All six exact numerical bounds in Appendix A.3.6 on a compact time interval. -/
theorem appendix_raw_domination {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) (x : Space d) :
    |rawKL μ ν t x| ≤ PJ M T x ∧
    |deriv (fun s => rawKL μ ν s x) t| ≤ QJ M T x ∧
    |rawChi μ ν t x| ≤ PC M T x ∧
    |deriv (fun s => rawChi μ ν s x) t| ≤ QC M T x ∧
    |rawAffinity μ ν t x| ≤ PA M T x ∧
    |deriv (fun s => rawAffinity μ ν s x) t| ≤ QA M T x :=
  ⟨rawKL_bound hM μ ν hT ht x, rawKL_deriv_bound hM μ ν hT ht x,
    rawChi_bound hM μ ν hT ht x, rawChi_deriv_bound hM μ ν hT ht x,
    rawAffinity_bound hM μ ν hT ht x, rawAffinity_deriv_bound hM μ ν hT ht x⟩

omit ν [IsProbabilityMeasure ν] in
/-- Equation (A.44): the time derivative is integrable and has zero integral. -/
theorem integral_density_deriv_zero (t : ℝ) :
    Integrable (fun x => deriv (fun s => meanScaledDensity μ s x) t) ∧
    (∫ x, deriv (fun s => meanScaledDensity μ s x) t) = 0 := by
  have hg (x : Space d) : HasGradientAt (fun _ : Space d => (1 : ℝ)) (0 : Space d) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x
  have h := lemma2_with_gradient_field hM μ (fun _ => 1) (fun _ => 0)
    continuous_const continuous_const hg (L := 1) (c := 0) (by norm_num) (by norm_num)
    (fun x => by simp) t
  exact ⟨by simpa using h.1, by simpa using h.2.2⟩

/-- The exact S(c;d) from Lemma 3. -/
def appendixS (c : ℝ) (d : ℕ) : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * exp (c ^ 2)

/-- The exact K(c;d,k) from Lemma 3. -/
def appendixK (c : ℝ) (d k : ℕ) : ℝ :=
  (2 : ℝ) ^ ((k : ℝ) + (d : ℝ) / 2) * (k.factorial : ℝ) * exp ((c + 1) ^ 2)

/-- Equation (A.45), uniformly in both interpolation time and mixing vector. -/
theorem gaussian_component_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T)
    (θ : Ball d M) (x : Space d) :
    phi (x - t • θ.val) ≤ phi x * exp (T * M * ‖x‖) := by
  have h := (density_envelopes hM (Measure.dirac θ) hT ht x).2
  simpa [meanScaledDensity] using h

/-- Equation (A.46), with the actual component time derivative. -/
theorem gaussian_component_deriv_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T)
    (θ : Ball d M) (x : Space d) :
    |deriv (fun s : ℝ => phi (x - s • θ.val)) t| ≤
      (M * ‖x‖ + T * M ^ 2) * phi x * exp (T * M * ‖x‖) := by
  rw [(phi_mean_scaling_hasDerivAt θ.val x t).deriv, abs_mul,
    abs_of_pos (phi_pos _)]
  have ha : 0 ≤ densityTimeEnvelope M T x := by unfold densityTimeEnvelope; positivity
  calc
    _ ≤ densityTimeEnvelope M T x * phi (x - t • θ.val) :=
      mul_le_mul_of_nonneg_right (density_time_weight_bound hM hT ht θ x) (phi_pos _).le
    _ ≤ densityTimeEnvelope M T x * (phi x * exp (T * M * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (gaussian_component_bound hM hT ht θ x) ha
    _ = _ := by unfold densityTimeEnvelope; ring

omit hM in
theorem integral_PC_bound (T : ℝ) :
    (∫ x : Space d, PC M T x) ≤ exp (T ^ 2 * M ^ 2 / 2) * appendixS (3 * T * M) d := by
  unfold PC
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (lemma3_exponential d (3 * T * M)) (exp_pos _).le

theorem integral_QC_bound {T : ℝ} (hT : 0 ≤ T) :
    (∫ x : Space d, QC M T x) ≤
      (4 * T * M ^ 2 * exp (T ^ 2 * M ^ 2)) * appendixS (5 * T * M) d +
      (4 * M * exp (T ^ 2 * M ^ 2)) * appendixK (5 * T * M) d 1 := by
  have h0 := integrable_phi_mul_exp_norm d (5 * T * M)
  have h1 : Integrable (fun x : Space d => phi x * (1 + ‖x‖) * exp (5 * T * M * ‖x‖)) := by
    simpa using integrable_gaussian_polynomial_exponential d (5 * T * M) 1
  have hk : (∫ x : Space d, phi x * (1 + ‖x‖) * exp (5 * T * M * ‖x‖)) ≤
      appendixK (5 * T * M) d 1 := by
    simpa [appendixK] using lemma3_polynomial d (5 * T * M) 1
  unfold QC
  rw [integral_add (h0.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (lemma3_exponential d _) (by positivity))
    (mul_le_mul_of_nonneg_left hk (by positivity))

/-- The full numerical PC+QC bound displayed on manuscript page 20. -/
theorem integral_PC_add_QC_bound {T : ℝ} (hT : 0 ≤ T) :
    (∫ x : Space d, PC M T x + QC M T x) ≤
      exp (T ^ 2 * M ^ 2 / 2) * appendixS (3 * T * M) d +
      (4 * T * M ^ 2 * exp (T ^ 2 * M ^ 2)) * appendixS (5 * T * M) d +
      (4 * M * exp (T ^ 2 * M ^ 2)) * appendixK (5 * T * M) d 1 := by
  have hi := appendix_envelopes_integrable (d := d) M T
  rw [integral_add hi.2.2.1 hi.2.2.2.1]
  have h := add_le_add (integral_PC_bound (d := d) (M := M) T) (integral_QC_bound (d := d) hM hT)
  simpa only [add_assoc] using h

omit hM in
theorem integral_PA_bound (T : ℝ) :
    (∫ x : Space d, PA M T x) ≤ appendixS (T * M) d :=
  lemma3_exponential d (T * M)

theorem integral_QA_bound {T : ℝ} (hT : 0 ≤ T) :
    (∫ x : Space d, QA M T x) ≤
      (T * M ^ 2 * exp (T ^ 2 * M ^ 2 / 4)) * appendixS (2 * T * M) d +
      (M * exp (T ^ 2 * M ^ 2 / 4)) * appendixK (2 * T * M) d 1 := by
  have h0 := integrable_phi_mul_exp_norm d (2 * T * M)
  have h1 : Integrable (fun x : Space d => phi x * (1 + ‖x‖) * exp (2 * T * M * ‖x‖)) := by
    simpa using integrable_gaussian_polynomial_exponential d (2 * T * M) 1
  have hk : (∫ x : Space d, phi x * (1 + ‖x‖) * exp (2 * T * M * ‖x‖)) ≤
      appendixK (2 * T * M) d 1 := by
    simpa [appendixK] using lemma3_polynomial d (2 * T * M) 1
  unfold QA
  rw [integral_add (h0.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (lemma3_exponential d _) (by positivity))
    (mul_le_mul_of_nonneg_left hk (by positivity))

/-- The full numerical PA+QA bound displayed on manuscript page 21. -/
theorem integral_PA_add_QA_bound {T : ℝ} (hT : 0 ≤ T) :
    (∫ x : Space d, PA M T x + QA M T x) ≤
      appendixS (T * M) d +
      (T * M ^ 2 * exp (T ^ 2 * M ^ 2 / 4)) * appendixS (2 * T * M) d +
      (M * exp (T ^ 2 * M ^ 2 / 4)) * appendixK (2 * T * M) d 1 := by
  have hi := appendix_envelopes_integrable (d := d) M T
  rw [integral_add hi.2.2.2.2.1 hi.2.2.2.2.2]
  have h := add_le_add (integral_PA_bound (d := d) (M := M) T) (integral_QA_bound (d := d) hM hT)
  simpa only [add_assoc] using h

/-- The finite explicit chi-square bound immediately following (A.51). -/
theorem chiSq_explicit_finiteness_bound {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T) :
    0 ≤ meanScalingChiSq μ ν t ∧
    meanScalingChiSq μ ν t ≤ exp (T ^ 2 * M ^ 2 / 2) * appendixS (3 * T * M) d - 1 := by
  have hf := finiteDivergences_meanScaled_global hM μ ν t
  constructor
  · exact chiSq_nonneg volume _ _ (hf.positive_q.mono fun _ hx => hx.le)
  · change chiSq volume (meanScaledDensity μ t) (meanScaledDensity ν t) ≤ _
    rw [hf.chiSq_eq]
    have hi : (∫ x : Space d, rawChi μ ν t x) ≤ ∫ x : Space d, PC M T x := by
      exact integral_mono hf.integrable_ratio_square
        (appendix_envelopes_integrable (d := d) M T).2.2.1
        (fun x => (le_abs_self _).trans (rawChi_bound hM μ ν hT ht x))
    exact sub_le_sub_right (hi.trans (integral_PC_bound (d := d) (M := M) T)) 1

end GaussianMixturePaper
