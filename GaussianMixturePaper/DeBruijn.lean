import GaussianMixturePaper.GlobalRegularity

/-!
# Concrete generalized de Bruijn identities

These are the three specializations discussed in Section 3, proved directly
from the established Gaussian score identity and Lemma 1. They hold at every
real time, including zero. This file does not assert the external general PDE
theorem or a formal identification of its differential operators.

The scalar Fisher trace is written as the integral of the squared Euclidean
score norm, as in the displayed trace formula immediately after (3.1).
-/
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
open scoped InnerProductSpace
namespace GaussianComparison.GaussianModel

/-- Actual likelihood score, defined by the spatial gradient. -/
def likelihoodScore {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M))
    (s : ℝ) (x : Space d) : Space d :=
  gradient (fun y => log (meanScaledDensity μ s y / meanScaledDensity ν s y)) x

/-- The Fisher trace with a specified nonnegative density weight. -/
def scoreFisherTrace {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M))
    (s : ℝ) (w : Space d → ℝ) : ℝ :=
  ∫ x, w x * ‖likelihoodScore μ ν s x‖ ^ 2

/-- The weight q*rho^2*f''(rho) for the KL generator is p. -/
def klFisherTrace {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  scoreFisherTrace μ ν s (meanScaledDensity μ s)

/-- For f(r)=(sqrt(r)-1)^2, the Fisher weight is sqrt(p*q)/2. -/
def hellingerFisherTrace {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  scoreFisherTrace μ ν s (fun x => sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) / 2)

/-- For f(r)=(r-1)^2, the Fisher weight is 2*p^2/q. -/
def chiSqFisherTrace {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) : ℝ :=
  scoreFisherTrace μ ν s (fun x => 2 * (meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x))

/-- The KL generator on positive arguments; its continuous extension at zero
is unnecessary because Gaussian mixture densities are strictly positive. -/
def klGenerator (r : ℝ) : ℝ := r * log r - r + 1

def hellingerGenerator (r : ℝ) : ℝ := (sqrt r - 1) ^ 2

def chiSqGenerator (r : ℝ) : ℝ := (r - 1) ^ 2

theorem klGenerator_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt klGenerator (log r) r := by
  convert! (((hasDerivAt_id r).mul (Real.hasDerivAt_log hr.ne')).sub
    (hasDerivAt_id r)).add_const 1 using 1
  simp only [id_eq]
  field_simp
  ring

theorem hellingerGenerator_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt hellingerGenerator (1 - (sqrt r)⁻¹) r := by
  convert! ((Real.hasDerivAt_sqrt hr.ne').sub_const 1).pow 2 using 1
  field_simp [(sqrt_pos.mpr hr).ne']
  ring

theorem chiSqGenerator_hasDerivAt (r : ℝ) :
    HasDerivAt chiSqGenerator (2 * (r - 1)) r := by
  convert! ((hasDerivAt_id r).sub_const 1).pow 2 using 1
  simp only [id_eq]
  ring

theorem klGenerator_secondDeriv {r : ℝ} (hr : 0 < r) :
    deriv (deriv klGenerator) r = r⁻¹ := by
  have he : deriv klGenerator =ᶠ[𝓝 r] log := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (klGenerator_hasDerivAt hx).deriv
  rw [he.deriv_eq]
  exact Real.deriv_log r

theorem hellingerGenerator_secondDeriv {r : ℝ} (hr : 0 < r) :
    deriv (deriv hellingerGenerator) r = (2 * r * sqrt r)⁻¹ := by
  have he : deriv hellingerGenerator =ᶠ[𝓝 r] (fun x => 1 - (sqrt x)⁻¹) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (hellingerGenerator_hasDerivAt hx).deriv
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const r (1 : ℝ)).sub
    ((Real.hasDerivAt_sqrt hr.ne').inv (sqrt_pos.mpr hr).ne')
  change HasDerivAt (fun x => 1 - (sqrt x)⁻¹) _ r at hd
  rw [hd.deriv]
  have hs := sq_sqrt hr.le
  field_simp [hr.ne', (sqrt_pos.mpr hr).ne']
  nlinarith

theorem chiSqGenerator_secondDeriv (r : ℝ) :
    deriv (deriv chiSqGenerator) r = 2 := by
  have he : deriv chiSqGenerator = (fun x => 2 * (x - 1)) :=
    funext fun x => (chiSqGenerator_hasDerivAt x).deriv
  rw [he]
  convert! (((hasDerivAt_id r).sub_const 1).const_mul 2).deriv using 1
  ring

theorem klGenerator_weight {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    q * (p / q) ^ 2 * deriv (deriv klGenerator) (p / q) = p := by
  rw [klGenerator_secondDeriv (div_pos hp hq)]
  field_simp

theorem hellingerGenerator_weight {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    q * (p / q) ^ 2 * deriv (deriv hellingerGenerator) (p / q) = sqrt (p * q) / 2 := by
  have hr : 0 < p / q := div_pos hp hq
  rw [hellingerGenerator_secondDeriv hr]
  have he : (p / q) ^ 2 * (2 * (p / q) * sqrt (p / q))⁻¹ = sqrt (p / q) / 2 := by
    have hs := sq_sqrt hr.le
    have hs2 : q * sqrt (p / q) ^ 2 = p := by
      rw [hs]
      field_simp
    field_simp [hr.ne', (sqrt_pos.mpr hr).ne']
    nlinarith [hs2]
  rw [mul_assoc, he, sqrt_div hp.le, sqrt_mul hp.le]
  have hs := sq_sqrt hq.le
  field_simp [(sqrt_pos.mpr hq).ne']
  nlinarith

theorem chiSqGenerator_weight {p q : ℝ} (hq : 0 < q) :
    q * (p / q) ^ 2 * deriv (deriv chiSqGenerator) (p / q) = 2 * (p ^ 2 / q) := by
  rw [chiSqGenerator_secondDeriv]
  field_simp

/-- Section 3's trace integral, with the actual second derivative of a generator. -/
def generatorFisherTrace {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M))
    (s : ℝ) (f : ℝ → ℝ) : ℝ :=
  scoreFisherTrace μ ν s (fun x => meanScaledDensity ν s x *
    (meanScaledDensity μ s x / meanScaledDensity ν s x) ^ 2 *
    deriv (deriv f) (meanScaledDensity μ s x / meanScaledDensity ν s x))

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem likelihoodScore_eq (s : ℝ) (x : Space d) :
    likelihoodScore μ ν s x = s • meanScaledGap μ ν s x :=
  gradient_log_meanScaledDensity_ratio hM μ ν s x

theorem likelihoodScore_norm_sq (s : ℝ) (x : Space d) :
    ‖likelihoodScore μ ν s x‖ ^ 2 = s ^ 2 * ‖meanScaledGap μ ν s x‖ ^ 2 := by
  rw [likelihoodScore_eq hM μ ν s x, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem scoreFisherTrace_eq (s : ℝ) (w : Space d → ℝ) :
    scoreFisherTrace μ ν s w = s ^ 2 * ∫ x, w x * ‖meanScaledGap μ ν s x‖ ^ 2 := by
  unfold scoreFisherTrace
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [likelihoodScore_norm_sq hM μ ν s x]
  ring

theorem integrable_scoreFisherTrace {s : ℝ} {w : Space d → ℝ}
    (hw : Integrable w) (hwc : Continuous w) :
    Integrable (fun x => w x * ‖likelihoodScore μ ν s x‖ ^ 2) := by
  have hi := (integrable_mul_meanScaledGap_sq hM μ ν s hw hwc).const_mul (s ^ 2)
  apply hi.congr
  filter_upwards [] with x
  rw [likelihoodScore_norm_sq hM μ ν s x]
  ring

theorem integrable_klFisherTrace (s : ℝ) :
    Integrable (fun x => meanScaledDensity μ s x * ‖likelihoodScore μ ν s x‖ ^ 2) :=
  integrable_scoreFisherTrace hM μ ν (integrable_meanScaledDensity_global μ s)
    (continuous_meanScaledDensity_space μ s)

theorem integrable_hellingerFisherTrace (s : ℝ) :
    Integrable (fun x => (sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) / 2) *
      ‖likelihoodScore μ ν s x‖ ^ 2) := by
  apply integrable_scoreFisherTrace hM μ ν
  · exact (finiteDivergences_meanScaled_global hM μ ν s).integrable_affinity.div_const 2
  · exact (((continuous_meanScaledDensity_space μ s).mul
      (continuous_meanScaledDensity_space ν s)).sqrt).div_const 2

theorem integrable_chiSqFisherTrace (s : ℝ) :
    Integrable (fun x => (2 * (meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x)) *
      ‖likelihoodScore μ ν s x‖ ^ 2) := by
  apply integrable_scoreFisherTrace hM μ ν
  · exact (finiteDivergences_meanScaled_global hM μ ν s).integrable_ratio_square.const_mul 2
  · exact continuous_const.mul (((continuous_meanScaledDensity_space μ s).pow 2).div
      (continuous_meanScaledDensity_space ν s) (fun x => (meanScaledDensity_pos hM ν s x).ne'))

/-- Equation (3.3) for the KL generator, without dividing by time. -/
theorem deBruijn_kl (s : ℝ) :
    s * deriv (fun r => kl volume (meanScaledDensity μ r) (meanScaledDensity ν r)) s =
      klFisherTrace μ ν s := by
  rw [(meanScalingKL_hasDerivAt hM μ ν s).deriv, klFisherTrace,
    scoreFisherTrace_eq hM μ ν]
  ring

/-- Equation (3.3) for squared Hellinger distance, with its exact factor 1/2. -/
theorem deBruijn_hellinger (s : ℝ) :
    s * deriv (meanScalingHellinger μ ν) s = hellingerFisherTrace μ ν s := by
  rw [(meanScalingHellinger_hasDerivAt_global hM μ ν s).deriv,
    hellingerFisherTrace, scoreFisherTrace_eq hM μ ν]
  unfold meanScalingHellingerRate
  have he : (∫ x, (sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) / 2) *
      ‖meanScaledGap μ ν s x‖ ^ 2) =
      (∫ x, sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) *
        ‖meanScaledGap μ ν s x‖ ^ 2) / 2 := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [he]
  ring

/-- Equation (3.3) for Pearson chi-square divergence. -/
theorem deBruijn_chiSq (s : ℝ) :
    s * deriv (meanScalingChiSq μ ν) s = chiSqFisherTrace μ ν s := by
  rw [(meanScalingChiSq_hasDerivAt hM μ ν s).deriv,
    chiSqFisherTrace, scoreFisherTrace_eq hM μ ν]
  unfold meanScalingChiSqRate
  have he : (∫ x, (2 * (meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x)) *
      ‖meanScaledGap μ ν s x‖ ^ 2) =
      2 * ∫ x, (meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x) *
        ‖meanScaledGap μ ν s x‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [he]
  ring

theorem generatorFisherTrace_kl (s : ℝ) :
    generatorFisherTrace μ ν s klGenerator = klFisherTrace μ ν s := by
  unfold generatorFisherTrace klFisherTrace
  congr 1
  funext x
  exact klGenerator_weight (meanScaledDensity_pos hM μ s x) (meanScaledDensity_pos hM ν s x)

theorem generatorFisherTrace_hellinger (s : ℝ) :
    generatorFisherTrace μ ν s hellingerGenerator = hellingerFisherTrace μ ν s := by
  unfold generatorFisherTrace hellingerFisherTrace
  congr 1
  funext x
  exact hellingerGenerator_weight (meanScaledDensity_pos hM μ s x) (meanScaledDensity_pos hM ν s x)

omit [IsProbabilityMeasure μ] in
theorem generatorFisherTrace_chiSq (s : ℝ) :
    generatorFisherTrace μ ν s chiSqGenerator = chiSqFisherTrace μ ν s := by
  unfold generatorFisherTrace chiSqFisherTrace
  congr 1
  funext x
  exact chiSqGenerator_weight (meanScaledDensity_pos hM ν s x)

/-- The concrete generalized de Bruijn identity for all three generators. -/
theorem deBruijn_three_generators (s : ℝ) :
    s * deriv (fun r => kl volume (meanScaledDensity μ r) (meanScaledDensity ν r)) s =
      generatorFisherTrace μ ν s klGenerator ∧
    s * deriv (meanScalingHellinger μ ν) s = generatorFisherTrace μ ν s hellingerGenerator ∧
    s * deriv (meanScalingChiSq μ ν) s = generatorFisherTrace μ ν s chiSqGenerator := by
  rw [generatorFisherTrace_kl hM μ ν, generatorFisherTrace_hellinger hM μ ν,
    generatorFisherTrace_chiSq hM μ ν]
  exact ⟨deBruijn_kl hM μ ν s, deBruijn_hellinger hM μ ν s, deBruijn_chiSq hM μ ν s⟩

end GaussianComparison.GaussianModel
