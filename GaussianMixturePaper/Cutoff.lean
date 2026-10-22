import GaussianComparison.MeanScalingIntegration
import GaussianMixturePaper.GaussianEnvelope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The literal cubic cutoff in Appendix A.3.4

This module uses the actual polynomial in (A.34), including its constant
pieces, rather than substituting a generic smooth bump function.
-/

noncomputable section

open Set Filter MeasureTheory Real
open scoped Topology InnerProductSpace NNReal

namespace GaussianMixturePaper
namespace PaperCutoff

def cubic (r : ℝ) : ℝ := 1 - 3 * (r - 1) ^ 2 + 2 * (r - 1) ^ 3

def cubicDeriv (r : ℝ) : ℝ := 6 * (r - 1) * (r - 2)

/-- The endpoint conventions use `≤`; the values at the joins coincide, so
this is exactly the piecewise formula (A.34), extended constantly to r<0. -/
def psi (r : ℝ) : ℝ := if r ≤ 1 then 1 else if r ≤ 2 then cubic r else 0

def psiDeriv (r : ℝ) : ℝ := if r ≤ 1 then 0 else if r ≤ 2 then cubicDeriv r else 0

@[simp] theorem cubic_one : cubic 1 = 1 := by norm_num [cubic]
@[simp] theorem cubic_two : cubic 2 = 0 := by norm_num [cubic]
@[simp] theorem cubicDeriv_one : cubicDeriv 1 = 0 := by norm_num [cubicDeriv]
@[simp] theorem cubicDeriv_two : cubicDeriv 2 = 0 := by norm_num [cubicDeriv]

theorem cubic_hasDerivAt (r : ℝ) : HasDerivAt cubic (cubicDeriv r) r := by
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 r := by
    simpa using (hasDerivAt_id r).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (r - 1)) r := by
    simpa using! h1.pow 2
  have h3 : HasDerivAt (fun x : ℝ => (x - 1) ^ 3) (3 * (r - 1) ^ 2) r := by
    simpa using! h1.pow 3
  have h := ((hasDerivAt_const r (1 : ℝ)).sub (h2.const_mul 3)).add (h3.const_mul 2)
  change HasDerivAt cubic (0 - 3 * (2 * (r - 1)) + 2 * (3 * (r - 1) ^ 2)) r at h
  exact h.congr_deriv (by unfold cubicDeriv; ring)

theorem psi_eq_one {r : ℝ} (hr : r ≤ 1) : psi r = 1 := by simp [psi, hr]

theorem psi_eq_cubic {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) : psi r = cubic r := by
  by_cases hr : r ≤ 1
  · have : r = 1 := le_antisymm hr h1
    simp [this, psi]
  · simp [psi, hr, h2]

theorem psi_eq_zero {r : ℝ} (hr : 2 ≤ r) : psi r = 0 := by
  by_cases h2 : r ≤ 2
  · have : r = 2 := le_antisymm h2 hr
    norm_num [this, psi]
  · have h1 : ¬r ≤ 1 := by linarith
    simp [psi, h1, h2]

theorem psi_hasDerivAt_one : HasDerivAt psi 0 1 := by
  have hl : HasDerivWithinAt psi 0 (Iic 1) 1 := by
    apply (hasDerivWithinAt_const 1 (Iic (1 : ℝ)) (1 : ℝ)).congr
    · intro r hr
      exact psi_eq_one hr
    · exact psi_eq_one le_rfl
  have hr : HasDerivWithinAt psi 0 (Icc 1 2) 1 := by
    apply (by simpa using (cubic_hasDerivAt 1).hasDerivWithinAt :
      HasDerivWithinAt cubic 0 (Icc 1 2) 1).congr
    · intro r hr
      exact psi_eq_cubic hr.1 hr.2
    · norm_num [psi, cubic]
  apply (hl.union hr).hasDerivAt
  apply Filter.mem_of_superset (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  intro r hr
  by_cases h : r ≤ 1
  · exact Or.inl h
  · exact Or.inr ⟨le_of_not_ge h, le_of_lt hr⟩

theorem psi_hasDerivAt_two : HasDerivAt psi 0 2 := by
  have hl : HasDerivWithinAt psi 0 (Icc 1 2) 2 := by
    apply (by simpa using (cubic_hasDerivAt 2).hasDerivWithinAt :
      HasDerivWithinAt cubic 0 (Icc 1 2) 2).congr
    · intro r hr
      exact psi_eq_cubic hr.1 hr.2
    · norm_num [psi, cubic]
  have hr : HasDerivWithinAt psi 0 (Ici 2) 2 := by
    apply (hasDerivWithinAt_const 2 (Ici (2 : ℝ)) (0 : ℝ)).congr
    · intro r hr
      exact psi_eq_zero hr
    · exact psi_eq_zero le_rfl
  apply (hl.union hr).hasDerivAt
  apply Filter.mem_of_superset (Ioi_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  intro r hr
  by_cases h : r ≤ 2
  · exact Or.inl ⟨le_of_lt hr, h⟩
  · exact Or.inr (le_of_not_ge h)

theorem psi_hasDerivAt (r : ℝ) : HasDerivAt psi (psiDeriv r) r := by
  rcases lt_trichotomy r 1 with h1 | h1 | h1
  · have hd : psiDeriv r = 0 := by simp [psiDeriv, h1.le]
    rw [hd]
    apply (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq
    exact Filter.eventually_of_mem (Iio_mem_nhds h1) fun s hs => psi_eq_one hs.le
  · subst r
    simpa [psiDeriv] using psi_hasDerivAt_one
  · rcases lt_trichotomy r 2 with h2 | h2 | h2
    · have hd : psiDeriv r = cubicDeriv r := by
        simp [psiDeriv, not_le.mpr h1, h2.le]
      rw [hd]
      apply (cubic_hasDerivAt r).congr_of_eventuallyEq
      exact Filter.eventually_of_mem (Ioo_mem_nhds h1 h2)
        fun s hs => psi_eq_cubic hs.1.le hs.2.le
    · subst r
      simpa [psiDeriv] using psi_hasDerivAt_two
    · have hd : psiDeriv r = 0 := by
        simp [psiDeriv, not_le.mpr h1, not_le.mpr h2]
      rw [hd]
      apply (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq
      exact Filter.eventually_of_mem (Ioi_mem_nhds h2) fun s hs => psi_eq_zero hs.le

theorem continuous_psiDeriv : Continuous psiDeriv := by
  have hc : Continuous cubicDeriv := by unfold cubicDeriv; fun_prop
  have hi : Continuous (fun r : ℝ => if r ≤ 2 then cubicDeriv r else 0) := by
    apply Continuous.if _ hc continuous_const
    intro r hr
    have : r = 2 := by simpa [show {x : ℝ | x ≤ 2} = Iic 2 from rfl] using hr
    simp [this]
  apply Continuous.if _ continuous_const hi
  intro r hr
  have : r = 1 := by simpa [show {x : ℝ | x ≤ 1} = Iic 1 from rfl] using hr
  simp [this]

theorem contDiff_psi : ContDiff ℝ 1 psi := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun r => (psi_hasDerivAt r).differentiableAt
  · have he : deriv psi = psiDeriv := funext fun r => (psi_hasDerivAt r).deriv
    rw [he]
    exact continuous_psiDeriv

theorem psi_range (r : ℝ) : 0 ≤ psi r ∧ psi r ≤ 1 := by
  by_cases h1 : r ≤ 1
  · simp [psi_eq_one h1]
  by_cases h2 : r ≤ 2
  · rw [psi_eq_cubic (le_of_not_ge h1) h2]
    have hu : 0 ≤ r - 1 := by linarith
    have hv : 0 ≤ 2 - r := by linarith
    have he : cubic r = (2 - r) ^ 2 * (2 * r - 1) := by unfold cubic; ring
    constructor
    · rw [he]
      exact mul_nonneg (sq_nonneg _) (by linarith)
    · have hh : 0 ≤ (r - 1) ^ 2 * (5 - 2 * r) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      dsimp [cubic]
      nlinarith
  · simp [psi_eq_zero (le_of_not_ge h2)]

theorem psiDeriv_bound (r : ℝ) : |psiDeriv r| ≤ 3 / 2 := by
  by_cases h1 : r ≤ 1
  · norm_num [psiDeriv, h1]
  by_cases h2 : r ≤ 2
  · have hnonpos : cubicDeriv r ≤ 0 := by
      dsimp [cubicDeriv]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    simp only [psiDeriv, if_neg h1, if_pos h2, abs_of_nonpos hnonpos]
    dsimp [cubicDeriv]
    nlinarith [sq_nonneg (r - 3 / 2)]
  · norm_num [psiDeriv, h1, h2]

theorem lipschitz_psi : LipschitzWith (3 / 2 : ℝ≥0) psi := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun r => (psi_hasDerivAt r).differentiableAt)
  intro r
  rw [← NNReal.coe_le_coe, coe_nnnorm, (psi_hasDerivAt r).deriv]
  simpa only [Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat] using psiDeriv_bound r

open GaussianComparison.GaussianModel

/-- The radial cutoff chi_R from (A.34). -/
def chi {d : ℕ} (R : ℝ) (x : Space d) : ℝ := psi (‖x‖ / R)

theorem chi_range {d : ℕ} (R : ℝ) (x : Space d) :
    0 ≤ chi R x ∧ chi R x ≤ 1 := psi_range _

theorem chi_eq_one {d : ℕ} {R : ℝ} (hR : 0 < R) {x : Space d}
    (hx : ‖x‖ ≤ R) : chi R x = 1 :=
  psi_eq_one ((div_le_one hR).2 hx)

theorem chi_eq_zero {d : ℕ} {R : ℝ} (hR : 0 < R) {x : Space d}
    (hx : 2 * R ≤ ‖x‖) : chi R x = 0 :=
  psi_eq_zero ((le_div_iff₀ hR).2 hx)

/-- Smoothness at zero uses the locally constant inner piece; no
differentiability of the norm at zero is assumed. -/
theorem contDiff_chi {d : ℕ} {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ 1 (chi (d := d) R) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    have hn : {y : Space d | ‖y‖ < R} ∈ 𝓝 (0 : Space d) :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hR)
    exact Filter.eventually_of_mem hn fun y hy => chi_eq_one hR hy.le
  · exact contDiff_psi.contDiffAt.comp x ((contDiffAt_norm ℝ hx).div_const R)

theorem chi_hasCompactSupport {d : ℕ} {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (chi (d := d) R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space d) (2 * R))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (chi_eq_zero hR (le_of_lt (lt_of_not_ge hn)))

theorem lipschitz_chi {d : ℕ} {R : ℝ} (hR : 0 < R) :
    LipschitzWith ⟨3 / (2 * R), by positivity⟩ (chi (d := d) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (chi R x) (chi R y) ≤ (3 / 2 : ℝ) * dist (‖x‖ / R) (‖y‖ / R) := by
      simpa only [chi, NNReal.coe_div, NNReal.coe_ofNat] using
        lipschitz_psi.dist_le_mul (‖x‖ / R) (‖y‖ / R)
    _ = (3 / (2 * R)) * |‖x‖ - ‖y‖| := by
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hR]
      ring
    _ ≤ (3 / (2 * R)) * dist x y := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by positivity)

/-- Equation (A.36), including points at both joins and the origin. -/
theorem gradient_chi_bound {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Space d) :
    ‖gradient (chi R) x‖ ≤ 3 / (2 * R) := by
  simpa [gradient] using!
    (norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (lipschitz_chi hR))

theorem chi_hasGradientAt {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Space d) :
    HasGradientAt (chi R) (gradient (chi R) x) x :=
  ((contDiff_chi hR).differentiable one_ne_zero x).hasGradientAt

theorem continuous_gradient_chi {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Continuous (gradient (chi (d := d) R)) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
    ((contDiff_chi hR).continuous_fderiv one_ne_zero)

/-- The cutoffs eventually equal one at each fixed spatial point. -/
theorem chi_eventually_one {d : ℕ} (x : Space d) :
    ∀ᶠ R : ℝ in atTop, chi R x = 1 := by
  filter_upwards [eventually_gt_atTop (max ‖x‖ 0)] with R hR
  exact chi_eq_one (lt_of_le_of_lt (le_max_right _ _) hR)
    (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hR))

theorem tendsto_chi {d : ℕ} (x : Space d) :
    Tendsto (fun R : ℝ => chi R x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((chi_eventually_one x).mono fun _R hR => hR.symm)

/-- The boundary term (T2) in (A.37); for the paper, take
`A x = phi (x-t•theta) * g x`. -/
def boundaryTerm {d : ℕ} (μ : Measure (Space d))
    (A : Space d → ℝ) (θ : Space d) (R : ℝ) : ℝ :=
  ∫ x, A x * ⟪θ, gradient (chi R) x⟫_ℝ ∂μ

theorem inner_gradient_chi_bound {d : ℕ} {R M : ℝ} (hR : 0 < R)
    {θ : Space d} (hθ : ‖θ‖ ≤ M) (x : Space d) :
    ‖⟪θ, gradient (chi R) x⟫_ℝ‖ ≤ 3 * M / (2 * R) := by
  calc
    _ ≤ ‖θ‖ * ‖gradient (chi R) x‖ := norm_inner_le_norm _ _
    _ ≤ M * (3 / (2 * R)) :=
      mul_le_mul hθ (gradient_chi_bound hR x) (norm_nonneg _)
        ((norm_nonneg θ).trans hθ)
    _ = _ := by ring

theorem boundaryTerm_integrable {d : ℕ} {μ : Measure (Space d)}
    {A : Space d → ℝ} (hA : Integrable A μ) (θ : Space d)
    {R : ℝ} (hR : 0 < R) :
    Integrable (fun x => A x * ⟪θ, gradient (chi R) x⟫_ℝ) μ := by
  exact hA.mul_bdd
    (continuous_const.inner (continuous_gradient_chi hR)).aestronglyMeasurable
    (Filter.Eventually.of_forall (inner_gradient_chi_bound hR (θ := θ) le_rfl))

/-- The precise `1/R` boundary estimate used in the proof of Lemma 2. -/
theorem boundaryTerm_bound {d : ℕ} {μ : Measure (Space d)}
    {A : Space d → ℝ} (hA : Integrable A μ) {θ : Space d}
    {R M : ℝ} (hR : 0 < R) (hθ : ‖θ‖ ≤ M) :
    |boundaryTerm μ A θ R| ≤ (3 * M / (2 * R)) * (∫ x, |A x| ∂μ) := by
  have hh := norm_integral_le_of_norm_le
    (hA.norm.const_mul (3 * M / (2 * R)))
    (Filter.Eventually.of_forall fun x =>
      calc
        ‖A x * ⟪θ, gradient (chi R) x⟫_ℝ‖ =
            ‖A x‖ * ‖⟪θ, gradient (chi R) x⟫_ℝ‖ := norm_mul _ _
        _ ≤ ‖A x‖ * (3 * M / (2 * R)) :=
          mul_le_mul_of_nonneg_left (inner_gradient_chi_bound hR hθ x) (norm_nonneg _)
        _ = (3 * M / (2 * R)) * ‖A x‖ := mul_comm _ _)
  simpa only [boundaryTerm, Real.norm_eq_abs, integral_const_mul] using! hh

/-- Substituting the Gaussian domination bound `B = L*S(c+TM;d)` gives the
displayed bound for (T2) on page 16. -/
theorem boundaryTerm_bound_of_integral_bound {d : ℕ} {μ : Measure (Space d)}
    {A : Space d → ℝ} (hA : Integrable A μ) {θ : Space d}
    {R M B : ℝ} (hR : 0 < R) (hθ : ‖θ‖ ≤ M)
    (hB : (∫ x, |A x| ∂μ) ≤ B) :
    |boundaryTerm μ A θ R| ≤ 3 * M * B / (2 * R) := by
  have hM : 0 ≤ M := (norm_nonneg θ).trans hθ
  calc
    _ ≤ (3 * M / (2 * R)) * (∫ x, |A x| ∂μ) := boundaryTerm_bound hA hR hθ
    _ ≤ (3 * M / (2 * R)) * B := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := by ring

theorem tendsto_boundaryTerm {d : ℕ} {μ : Measure (Space d)}
    {A : Space d → ℝ} (hA : Integrable A μ) (θ : Space d) :
    Tendsto (boundaryTerm μ A θ) atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun R : ℝ => (3 * ‖θ‖ / (2 * R)) * (∫ x, |A x| ∂μ)) atTop (𝓝 0) := by
    have hh := (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).const_mul
      (3 * ‖θ‖ / 2 * (∫ x, |A x| ∂μ))
    have he : (fun R : ℝ => (3 * ‖θ‖ / (2 * R)) * (∫ x, |A x| ∂μ)) =
        (fun R : ℝ => (3 * ‖θ‖ / 2 * (∫ x, |A x| ∂μ)) * R⁻¹) := by
      funext R
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he]
    simpa using hh
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simpa only [Real.norm_eq_abs] using boundaryTerm_bound hA hR (θ := θ) le_rfl

/-- Dominated convergence for the literal cutoffs. This is the limiting step
for the left side and (T1) in (A.37). -/
theorem tendsto_integral_mul_chi {d : ℕ} {μ : Measure (Space d)}
    {A : Space d → ℝ} (hA : Integrable A μ) :
    Tendsto (fun R : ℝ => ∫ x, A x * chi R x ∂μ) atTop (𝓝 (∫ x, A x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖A x‖)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact hA.aestronglyMeasurable.mul (contDiff_chi hR).continuous.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs (chi R x), abs_of_nonneg (chi_range R x).1]
      exact mul_le_of_le_one_right (norm_nonneg _) (chi_range R x).2
  · exact hA.norm
  · exact Filter.Eventually.of_forall fun x => by
      simpa using (tendsto_chi x).const_mul (A x)

/-- The compact-support integration-by-parts calculation (A.37), with the
product-rule terms displayed separately. All integral existence is discharged
from continuity and the compact support of this explicit chi_R. -/
theorem cutoff_integration_by_parts {d : ℕ} {κ g : Space d → ℝ}
    (hκ : ContDiff ℝ 1 κ) (hg : ContDiff ℝ 1 g)
    (θ : Space d) {R : ℝ} (hR : 0 < R) :
    -(∫ x, fderiv ℝ κ x θ * (g x * chi R x)) =
      (∫ x, κ x * chi R x * fderiv ℝ g x θ) +
        boundaryTerm volume (fun x => κ x * g x) θ R := by
  let F : Space d → ℝ := fun x => g x * chi R x
  have hc := contDiff_chi (d := d) hR
  have hs := chi_hasCompactSupport (d := d) hR
  have hF : ContDiff ℝ 1 F := hg.mul hc
  have hFs : HasCompactSupport F := hs.mul_left
  have hk' : Continuous (fun x => fderiv ℝ κ x θ) :=
    (hκ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x θ) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hc' : Continuous (fun x => fderiv ℝ (chi R) x θ) :=
    (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF' : Continuous (fun x => fderiv ℝ F x θ) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h1 : Integrable (fun x => fderiv ℝ κ x θ * F x) :=
    (hk'.mul hF.continuous).integrable_of_hasCompactSupport hFs.mul_left
  have h2 : Integrable (fun x => κ x * fderiv ℝ F x θ) :=
    (hκ.continuous.mul hF').integrable_of_hasCompactSupport
      (hFs.fderiv_apply ℝ θ).mul_left
  have h0 : Integrable (fun x => κ x * F x) :=
    (hκ.continuous.mul hF.continuous).integrable_of_hasCompactSupport hFs.mul_left
  have ht1 : Integrable (fun x => κ x * chi R x * fderiv ℝ g x θ) :=
    ((hκ.continuous.mul hc.continuous).mul hg').integrable_of_hasCompactSupport
      hs.mul_left.mul_right
  have ht2 : Integrable (fun x => κ x * g x * fderiv ℝ (chi R) x θ) :=
    ((hκ.continuous.mul hg.continuous).mul hc').integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ θ).mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h0
    (fun x _ => hκ.differentiable one_ne_zero x)
    (fun x _ => hF.differentiable one_ne_zero x)
  calc
    _ = ∫ x, κ x * fderiv ℝ F x θ := hibp.symm
    _ = ∫ x, (κ x * chi R x * fderiv ℝ g x θ) +
        (κ x * g x * fderiv ℝ (chi R) x θ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [F]
      rw [fderiv_fun_mul (hg.differentiable one_ne_zero x)
        (hc.differentiable one_ne_zero x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    _ = (∫ x, κ x * chi R x * fderiv ℝ g x θ) +
        (∫ x, κ x * g x * fderiv ℝ (chi R) x θ) := integral_add ht1 ht2
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [(chi_hasGradientAt hR x).fderiv_apply, real_inner_comm]

/-- Sending the explicit cubic cutoff radius to infinity in (A.37). -/
theorem integration_by_parts_via_cutoff {d : ℕ} {κ g : Space d → ℝ}
    (hκ : ContDiff ℝ 1 κ) (hg : ContDiff ℝ 1 g) (θ : Space d)
    (h0 : Integrable (fun x => κ x * g x))
    (h1 : Integrable (fun x => fderiv ℝ κ x θ * g x))
    (h2 : Integrable (fun x => κ x * fderiv ℝ g x θ)) :
    -(∫ x, fderiv ℝ κ x θ * g x) = ∫ x, κ x * fderiv ℝ g x θ := by
  have hl := (tendsto_integral_mul_chi h1).neg
  have hr := (tendsto_integral_mul_chi h2).add (tendsto_boundaryTerm h0 θ)
  have he : (fun R : ℝ => -(∫ x, (fderiv ℝ κ x θ * g x) * chi R x)) =ᶠ[atTop]
      (fun R => (∫ x, (κ x * fderiv ℝ g x θ) * chi R x) +
        boundaryTerm volume (fun x => κ x * g x) θ R) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    convert! cutoff_integration_by_parts hκ hg θ hR using 1 <;>
      congr 1 <;> congr 1 <;> funext x <;> ring
  simpa using tendsto_nhds_unique (hl.congr' he) hr

/-- The upper Gaussian-shift envelope used in (A.36), before mixing. -/
theorem shifted_gaussian_envelope {d : ℕ} {M T t : ℝ}
    (hM : 0 ≤ M) (ht : |t| ≤ T) (θ : Ball d M) (x : Space d) :
    phi (x - t • θ.val) ≤ phi x * exp (T * M * ‖x‖) := by
  rw [← phi_mul_kernel_mean_scaling]
  apply mul_le_mul_of_nonneg_left _ (phi_pos x).le
  refine (kernel_le_of_nonneg_time θ (t • x) (sq_nonneg t)).trans ?_
  apply exp_le_exp.mpr
  rw [norm_smul, Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_right ht (mul_nonneg hM (norm_nonneg x))]

/-- The integrable exponential envelope for κg, with the exact exponent c+TM. -/
theorem shifted_gaussian_mul_envelope {d : ℕ} {M T t L c : ℝ}
    (hM : 0 ≤ M) (ht : |t| ≤ T) (θ : Ball d M)
    {g : Space d → ℝ} (hbound : ∀ x, |g x| ≤ L * exp (c * ‖x‖)) (x : Space d) :
    |phi (x - t • θ.val) * g x| ≤ L * (phi x * exp ((c + T * M) * ‖x‖)) := by
  rw [abs_mul, abs_of_pos (phi_pos _)]
  calc
    _ ≤ phi (x - t • θ.val) * (L * exp (c * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (hbound x) (phi_pos _).le
    _ ≤ (phi x * exp (T * M * ‖x‖)) * (L * exp (c * ‖x‖)) :=
      mul_le_mul_of_nonneg_right (shifted_gaussian_envelope hM ht θ x)
        ((abs_nonneg (g x)).trans (hbound x))
    _ = _ := by rw [add_mul, exp_add]; ring

theorem shifted_gaussian_mul_integrable {d : ℕ} {M T t L c : ℝ}
    (hM : 0 ≤ M) (ht : |t| ≤ T) (θ : Ball d M)
    {g : Space d → ℝ} (hg : Continuous g)
    (hbound : ∀ x, |g x| ≤ L * exp (c * ‖x‖)) :
    Integrable (fun x => phi (x - t • θ.val) * g x) := by
  apply ((integrable_phi_mul_exp_norm d (c + T * M)).const_mul L).mono'
    ((by unfold phi; fun_prop : Continuous (fun x : Space d => phi (x - t • θ.val))).mul
      hg).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using! shifted_gaussian_mul_envelope hM ht θ hbound x

/-- The absolute-integral bound L S(c+TM;d) from (A.36). -/
theorem shifted_gaussian_abs_integral_bound {d : ℕ} {M T t L c : ℝ}
    (hM : 0 ≤ M) (ht : |t| ≤ T) (θ : Ball d M)
    {g : Space d → ℝ} (hg : Continuous g) (hL : 0 ≤ L)
    (hbound : ∀ x, |g x| ≤ L * exp (c * ‖x‖)) :
    (∫ x, |phi (x - t • θ.val) * g x|) ≤
      L * ((2 : ℝ) ^ ((d : ℝ) / 2) * exp ((c + T * M) ^ 2)) := by
  have hi := shifted_gaussian_mul_integrable hM ht θ hg hbound
  calc
    _ ≤ ∫ x : Space d, L * (phi x * exp ((c + T * M) * ‖x‖)) := by
      apply integral_mono hi.abs ((integrable_phi_mul_exp_norm d _).const_mul L)
      exact shifted_gaussian_mul_envelope hM ht θ hbound
    _ = L * (∫ x : Space d, phi x * exp ((c + T * M) * ‖x‖)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma3_exponential d _) hL

/-- The exact boundary error in (A.37): 3ML S(c+TM;d)/(2R). -/
theorem gaussian_boundaryTerm_bound {d : ℕ} {M T t L c R : ℝ}
    (hM : 0 ≤ M) (ht : |t| ≤ T) (θ : Ball d M)
    {g : Space d → ℝ} (hg : Continuous g) (hL : 0 ≤ L)
    (hbound : ∀ x, |g x| ≤ L * exp (c * ‖x‖)) (hR : 0 < R) :
    |boundaryTerm volume (fun x => phi (x - t • θ.val) * g x) θ.val R| ≤
      3 * M * L * ((2 : ℝ) ^ ((d : ℝ) / 2) * exp ((c + T * M) ^ 2)) / (2 * R) := by
  have hb := boundaryTerm_bound_of_integral_bound
    (shifted_gaussian_mul_integrable hM ht θ hg hbound) hR θ.property
    (shifted_gaussian_abs_integral_bound hM ht θ hg hL hbound)
  convert! hb using 1; ring

/-- Equation (A.38), derived through the literal cutoff identity and its limits.
Every whole-space integrability obligation is proved from the manuscript's
C¹ and exponential-growth assumption (A.2). -/
theorem gaussian_integration_by_parts_via_cutoff {d : ℕ} {M L c : ℝ}
    (hM : 0 ≤ M) (θ : Ball d M) {g : Space d → ℝ}
    (hg : ContDiff ℝ 1 g) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hbound : ∀ x, |g x| + ‖gradient g x‖ ≤ L * exp (c * ‖x‖)) (t : ℝ) :
    (∫ x, (⟪θ.val, x⟫_ℝ - t * ‖θ.val‖ ^ 2) * phi (x - t • θ.val) * g x) =
      ∫ x, phi (x - t • θ.val) * ⟪θ.val, gradient g x⟫_ℝ := by
  let K : Space d → ℝ := fun x => kernel θ.val (t • x) (t ^ 2)
  let W : Space d → ℝ := fun x => ⟪θ.val, x⟫_ℝ - t * ‖θ.val‖ ^ 2
  have hK : ExpGrowth (fun (_ : Unit) x => K x) :=
    (scaledKernel_growth hM (abs_nonneg t)).reparam (fun _ => (⟨t, le_rfl⟩, θ))
  have hW : ExpGrowth (fun (_ : Unit) x => W x) :=
    (scaledWeight_growth hM (abs_nonneg t)).reparam (fun _ => (⟨t, le_rfl⟩, θ))
  have hgbound (x) : |g x| ≤ L * exp (c * ‖x‖) :=
    (le_add_of_nonneg_right (norm_nonneg (gradient g x))).trans (hbound x)
  have hgb : ExpGrowth (fun (_ : Unit) x => g x) := by
    refine ⟨L, c, hL, hc, fun _ x => ?_⟩
    simpa only [Real.norm_eq_abs] using hgbound x
  have hGb : ExpGrowth (fun (_ : Unit) x => gradient g x) :=
    ⟨L, c, hL, hc, fun _ x =>
      (le_add_of_nonneg_left (abs_nonneg (g x))).trans (hbound x)⟩
  have hθb : ExpGrowth (fun (_ : Unit) (_ : Space d) => θ.val) :=
    ExpGrowth.of_bounded M hM (fun _ _ => θ.property)
  have hGc : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
      (hg.continuous_fderiv one_ne_zero)
  have hgrad (x) : HasGradientAt g (gradient g x) x :=
    (hg.differentiable one_ne_zero x).hasGradientAt
  have hKc : Continuous K := by unfold K kernel; fun_prop
  have hWc : Continuous W := by unfold W; fun_prop
  have hi₁ : Integrable (fun x => W x * phi (x - t • θ.val) * g x) := by
    convert! ((hK.mul hW).mul hgb).gaussian_integrable ()
      ((hKc.mul hWc).mul hg.continuous).aestronglyMeasurable using 1
    funext x
    rw [← phi_mul_kernel_mean_scaling]
    dsimp [K]
    ring
  have hi₂ : Integrable (fun x => phi (x - t • θ.val) * ⟪θ.val, gradient g x⟫_ℝ) := by
    convert! (hK.mul (hθb.inner hGb)).gaussian_integrable ()
      (hKc.mul (continuous_const.inner hGc)).aestronglyMeasurable using 1
    funext x
    rw [← phi_mul_kernel_mean_scaling]
    dsimp [K]
    ring
  have hi₀ := shifted_gaussian_mul_integrable hM (le_rfl : |t| ≤ |t|) θ
    hg.continuous hgbound
  have hκ : ContDiff ℝ 1 (fun x : Space d => phi (x - t • θ.val)) := by
    have hp : ContDiff ℝ 1 (phi (d := d)) := by
      unfold phi
      exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const 2).exp)
    exact hp.comp (contDiff_id.sub contDiff_const)
  have hpd (x : Space d) :
      fderiv ℝ (fun y => phi (y - t • θ.val)) x θ.val =
        -(W x * phi (x - t • θ.val)) := by
    rw [phi_sub_fderiv]
    dsimp [W]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_comm x θ.val]
    ring
  have h₁ : Integrable (fun x =>
      fderiv ℝ (fun y => phi (y - t • θ.val)) x θ.val * g x) := by
    simp_rw [hpd, neg_mul]
    exact hi₁.neg
  have h₂ : Integrable (fun x => phi (x - t • θ.val) * fderiv ℝ g x θ.val) := by
    convert! hi₂ using 1
    funext x
    rw [(hgrad x).fderiv_apply, real_inner_comm]
  have he := integration_by_parts_via_cutoff hκ hg θ.val hi₀ h₁ h₂
  simp_rw [hpd, neg_mul, integral_neg, neg_neg, (hgrad _).fderiv_apply] at he
  convert! he using 1
  congr 1
  funext x
  rw [real_inner_comm]

/-- Lemma 2, now with the literal Appendix A.3.4 cutoff route all the way
through Fubini. The hypotheses are exactly C¹ and the exponential bound (A.2);
no boundary, PDE, integrability, or integration-by-parts certificate is assumed. -/
theorem lemma2_via_cutoff {d : ℕ} {M L c : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ]
    {g : Space d → ℝ} (hg : ContDiff ℝ 1 g) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hbound : ∀ x, |g x| + ‖gradient g x‖ ≤ L * exp (c * ‖x‖)) (t : ℝ) :
    Integrable (fun x => deriv (fun s => meanScaledDensity μ s x) t * g x) ∧
    Integrable (fun x => meanScaledDensity μ t x *
      ⟪gradient g x, meanScaledPosterior μ t x⟫_ℝ) ∧
    (∫ x, deriv (fun s => meanScaledDensity μ s x) t * g x) =
      ∫ x, meanScaledDensity μ t x * ⟪gradient g x, meanScaledPosterior μ t x⟫_ℝ := by
  have hdt (x : Space d) : deriv (fun s => meanScaledDensity μ s x) t =
      phi x * scaledPartitionDot μ t x := by
    have hd := (scaledPartition_hasDerivAt μ t x).const_mul (phi x)
    have he : (fun s => meanScaledDensity μ s x) =
        (fun s => phi x * scaledPartition μ s x) := by
      funext s
      exact meanScaledDensity_eq_partition μ s x
    rw [he]
    exact hd.deriv
  have hgb : ExpGrowth (fun (_ : Unit) x => g x) := by
    refine ⟨L, c, hL, hc, fun _ x => ?_⟩
    simpa only [Real.norm_eq_abs] using
      (le_add_of_nonneg_right (norm_nonneg (gradient g x))).trans (hbound x)
  have hGb : ExpGrowth (fun (_ : Unit) x => gradient g x) :=
    ⟨L, c, hL, hc, fun _ x =>
      (le_add_of_nonneg_left (abs_nonneg (g x))).trans (hbound x)⟩
  have hGc : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
      (hg.continuous_fderiv one_ne_zero)
  have hi₁ := integrable_scaledPartitionDot_mul hM μ t hg.continuous hgb
  have hi₂ := integrable_meanScaledDensity_mul_inner hM μ t hGc hGb
  simp_rw [hdt]
  have heinner : (fun x => meanScaledDensity μ t x *
      ⟪gradient g x, meanScaledPosterior μ t x⟫_ℝ) =
      (fun x => meanScaledDensity μ t x *
      ⟪meanScaledPosterior μ t x, gradient g x⟫_ℝ) := by
    funext x
    rw [real_inner_comm]
  rw [heinner]
  refine ⟨hi₁, hi₂, ?_⟩
  let r : {s : ℝ // |s| ≤ |t|} := ⟨t, le_rfl⟩
  let K := fun (θ : Ball d M) (x : Space d) => kernel θ.val (t • x) (t ^ 2)
  let W := fun (θ : Ball d M) (x : Space d) => ⟪θ.val, x⟫_ℝ - t * ‖θ.val‖ ^ 2
  have hK : ExpGrowth K := (scaledKernel_growth hM (abs_nonneg t)).reparam (fun θ => (r, θ))
  have hW : ExpGrowth W := (scaledWeight_growth hM (abs_nonneg t)).reparam (fun θ => (r, θ))
  have hθ : ExpGrowth (fun (θ : Ball d M) (_ : Space d) => θ.val) :=
    ExpGrowth.of_bounded M hM (fun θ _ => θ.property)
  have hF := hgb.reparam (fun (_ : Ball d M) => ())
  have hGrad := hGb.reparam (fun (_ : Ball d M) => ())
  have hb₁ := (hK.mul hW).mul hF
  have hb₂ := hK.mul (hθ.inner hGrad)
  have hc₁ : Continuous (fun p : Space d × Ball d M => K p.2 p.1 * W p.2 p.1 * g p.1) := by
    exact (by unfold K W kernel; fun_prop : Continuous (fun p : Space d × Ball d M =>
      K p.2 p.1 * W p.2 p.1)).mul (hg.continuous.comp continuous_fst)
  have hc₂ : Continuous (fun p : Space d × Ball d M => K p.2 p.1 * ⟪p.2.val, gradient g p.1⟫_ℝ) := by
    exact (by unfold K kernel; fun_prop : Continuous (fun p : Space d × Ball d M => K p.2 p.1)).mul
      (continuous_subtype_val.comp continuous_snd |>.inner (hGc.comp continuous_fst))
  have hp₁ := hb₁.gaussian_integrable_prod (μ := μ) hc₁.aestronglyMeasurable
  have hp₂ := hb₂.gaussian_integrable_prod (μ := μ) hc₂.aestronglyMeasurable
  calc
    (∫ x, phi x * scaledPartitionDot μ t x * g x) =
        ∫ x, ∫ θ, phi x * (K θ x * W θ x * g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      have heq : (∫ θ, K θ x * W θ x * g x ∂μ) =
          (∫ θ, W θ x * K θ x ∂μ) * g x := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with θ
        ring
      rw [integral_const_mul, heq]
      dsimp [scaledPartitionDot, K, W]
      ring
    _ = ∫ θ, (∫ x : Space d, phi x * (K θ x * W θ x * g x)) ∂μ := integral_integral_swap hp₁
    _ = ∫ θ, (∫ x : Space d, phi x * (K θ x * ⟪θ.val, gradient g x⟫_ℝ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with θ
      convert! gaussian_integration_by_parts_via_cutoff hM θ hg hL hc hbound t using 1 <;>
        (congr 1; funext x; rw [← phi_mul_kernel_mean_scaling]; dsimp [K, W]; ring)
    _ = ∫ x, ∫ θ, phi x * (K θ x * ⟪θ.val, gradient g x⟫_ℝ) ∂μ :=
      (integral_integral_swap hp₂).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [meanScaledDensity_mul_inner_posterior hM μ t x (gradient g x)]
      apply integral_congr_ae
      filter_upwards [] with θ
      rw [← phi_mul_kernel_mean_scaling]
      dsimp [K]
      ring

end PaperCutoff
end GaussianMixturePaper
