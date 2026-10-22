import GaussianComparison.GaussianModel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Exponential envelopes for elementary Gaussian integration. The parameter
type is arbitrary, so the same estimates cover a compact prior or a bounded
interval of interpolation parameters. -/

noncomputable section
open MeasureTheory Real Filter
open scoped Topology

namespace GaussianComparison.GaussianModel

def ExpGrowth {A E : Type*} [NormedAddCommGroup E] {d : ℕ}
    (f : A → Space d → E) : Prop :=
  ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ a x, ‖f a x‖ ≤ C * exp (c * ‖x‖)

namespace ExpGrowth
variable {A : Type*} {d : ℕ}

theorem const (c : ℝ) : ExpGrowth (fun (_ : A) (_ : Space d) => c) := by
  refine ⟨|c|, 0, abs_nonneg _, le_rfl, ?_⟩
  simp

theorem of_bounded {E : Type*} [NormedAddCommGroup E] {f : A → Space d → E}
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a x, ‖f a x‖ ≤ C) : ExpGrowth f := by
  exact ⟨C, 0, hC, le_rfl, by simpa using hb⟩

theorem mono {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : A → Space d → E} {g : A → Space d → F}
    (hf : ExpGrowth f) (h : ∀ a x, ‖g a x‖ ≤ ‖f a x‖) : ExpGrowth g := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf
  exact ⟨C, c, hC, hc, fun a x => (h a x).trans (hb a x)⟩

theorem reparam {B E : Type*} [NormedAddCommGroup E]
    {f : A → Space d → E} (hf : ExpGrowth f) (g : B → A) :
    ExpGrowth (fun b x => f (g b) x) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf
  exact ⟨C, c, hC, hc, fun b x => hb (g b) x⟩

theorem add {f g : A → Space d → ℝ} (hf : ExpGrowth f) (hg : ExpGrowth g) :
    ExpGrowth (fun a x => f a x + g a x) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf
  obtain ⟨D, e, hD, he, hd⟩ := hg
  refine ⟨C + D, c + e, by positivity, by positivity, fun a x => ?_⟩
  have hce : exp (c * ‖x‖) ≤ exp ((c + e) * ‖x‖) :=
    exp_le_exp.mpr (by nlinarith [norm_nonneg x])
  have hec : exp (e * ‖x‖) ≤ exp ((c + e) * ‖x‖) :=
    exp_le_exp.mpr (by nlinarith [norm_nonneg x])
  calc
    ‖f a x + g a x‖ ≤ ‖f a x‖ + ‖g a x‖ := norm_add_le _ _
    _ ≤ C * exp (c * ‖x‖) + D * exp (e * ‖x‖) := add_le_add (hb a x) (hd a x)
    _ ≤ C * exp ((c + e) * ‖x‖) + D * exp ((c + e) * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hce hC) (mul_le_mul_of_nonneg_left hec hD)
    _ = _ := by ring

theorem neg {f : A → Space d → ℝ} (hf : ExpGrowth f) :
    ExpGrowth (fun a x => -f a x) := hf.mono (by simp)

theorem sub {f g : A → Space d → ℝ} (hf : ExpGrowth f) (hg : ExpGrowth g) :
    ExpGrowth (fun a x => f a x - g a x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul {f g : A → Space d → ℝ} (hf : ExpGrowth f) (hg : ExpGrowth g) :
    ExpGrowth (fun a x => f a x * g a x) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf
  obtain ⟨D, e, hD, he, hd⟩ := hg
  refine ⟨C * D, c + e, by positivity, by positivity, fun a x => ?_⟩
  calc
    ‖f a x * g a x‖ = ‖f a x‖ * ‖g a x‖ := norm_mul _ _
    _ ≤ (C * exp (c * ‖x‖)) * (D * exp (e * ‖x‖)) :=
      mul_le_mul (hb a x) (hd a x) (norm_nonneg _) (by positivity)
    _ = _ := by rw [add_mul, exp_add]; ring

theorem norm {E : Type*} [NormedAddCommGroup E] {f : A → Space d → E}
    (hf : ExpGrowth f) : ExpGrowth (fun a x => ‖f a x‖) :=
  hf.mono (by simp)

theorem smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : A → Space d → ℝ} {g : A → Space d → E}
    (hf : ExpGrowth f) (hg : ExpGrowth g) : ExpGrowth (fun a x => f a x • g a x) := by
  apply (hf.norm.mul hg.norm).mono
  intro a x
  simp [norm_smul]

theorem inner {f g : A → Space d → Space d} (hf : ExpGrowth f) (hg : ExpGrowth g) :
    ExpGrowth (fun a x => inner ℝ (f a x) (g a x)) := by
  apply (hf.norm.mul hg.norm).mono
  intro a x
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact abs_real_inner_le_norm _ _

theorem integral {B E : Type*} [MeasurableSpace B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure B} [IsProbabilityMeasure μ]
    {f : (A × B) → Space d → E} (hf : ExpGrowth f) :
    ExpGrowth (fun a x => ∫ b, f (a, b) x ∂μ) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf
  refine ⟨C, c, hC, hc, fun a x => ?_⟩
  simpa using norm_integral_le_of_norm_le_const
    (μ := μ) (Eventually.of_forall fun b => hb (a, b) x)

theorem radius : ExpGrowth (fun (_ : A) (x : Space d) => ‖x‖) := by
  refine ⟨1, 1, by norm_num, by norm_num, fun a x => ?_⟩
  simp only [Real.norm_of_nonneg (norm_nonneg _), one_mul]
  linarith [Real.add_one_le_exp ‖x‖]

theorem sqrt {f : A → Space d → ℝ} (hf : ExpGrowth f) :
    ExpGrowth (fun a x => sqrt (f a x)) := by
  apply ((const (A := A) (d := d) 1).add hf.norm).mono
  intro a x
  rw [Real.norm_of_nonneg (sqrt_nonneg _), Real.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖f a x‖)]
  exact (Real.sqrt_le_sqrt (le_abs_self _)).trans (by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [Real.norm_eq_abs]; nlinarith [abs_nonneg (f a x)])

theorem log {f : A → Space d → ℝ} (hf : ExpGrowth f)
    (hi : ExpGrowth (fun a x => (f a x)⁻¹)) (hp : ∀ a x, 0 < f a x) :
    ExpGrowth (fun a x => log (f a x)) := by
  apply (hf.add hi).mono
  intro a x
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (add_nonneg (hp a x).le (inv_pos.mpr (hp a x)).le)]
  apply abs_le.mpr
  constructor
  · have h := Real.log_le_self (inv_pos.mpr (hp a x)).le
    rw [Real.log_inv] at h
    linarith [hp a x]
  · linarith [Real.log_le_self (hp a x).le, inv_pos.mpr (hp a x)]

theorem gaussian_integrable {f : A → Space d → ℝ} (hf : ExpGrowth f)
    (a : A) (hm : AEStronglyMeasurable (f a) volume) :
    Integrable (fun x => phi x * f a x) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf
  apply ((integrable_phi_mul_exp_norm d c).const_mul C).mono'
    ((continuous_phi d).aestronglyMeasurable.mul hm)
  filter_upwards [] with x
  change ‖phi x * f a x‖ ≤ C * (phi x * exp (c * ‖x‖))
  rw [norm_mul, Real.norm_of_nonneg (phi_pos x).le]
  calc
    phi x * ‖f a x‖ ≤ phi x * (C * exp (c * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (hb a x) (phi_pos x).le
    _ = _ := by ring

theorem gaussian_integrable_prod [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    {f : A → Space d → ℝ} (hf : ExpGrowth f)
    (hm : AEStronglyMeasurable (fun p : Space d × A => f p.2 p.1) (volume.prod μ)) :
    Integrable (fun p : Space d × A => phi p.1 * f p.2 p.1) (volume.prod μ) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf
  have hi : Integrable (fun p : Space d × A => C * (phi p.1 * exp (c * ‖p.1‖)))
      (volume.prod μ) := by
    simpa using (((integrable_phi_mul_exp_norm d c).const_mul C).mul_prod
      (integrable_const (1 : ℝ) (μ := μ)))
  apply hi.mono' (((continuous_phi d).measurable.comp measurable_fst).aestronglyMeasurable.mul hm)
  filter_upwards [] with p
  change ‖phi p.1 * f p.2 p.1‖ ≤ C * (phi p.1 * exp (c * ‖p.1‖))
  rw [norm_mul, Real.norm_of_nonneg (phi_pos p.1).le]
  calc
    phi p.1 * ‖f p.2 p.1‖ ≤ phi p.1 * (C * exp (c * ‖p.1‖)) :=
      mul_le_mul_of_nonneg_left (hb p.2 p.1) (phi_pos p.1).le
    _ = _ := by ring

end ExpGrowth

/-- Differentiation under Gaussian volume, with the envelope and interchange
proved rather than assumed. -/
theorem hasDerivAt_gaussian_integral {d : ℕ} {F F' : ℝ → Space d → ℝ}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ s x, HasDerivAt (fun r => F r x) (F' s x) s)
    (hb : ∀ T : ℝ, 0 ≤ T → ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => F s.val x))
    (hb' : ∀ T : ℝ, 0 ≤ T → ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => F' s.val x))
    (t : ℝ) :
    HasDerivAt (fun s => ∫ x, phi x * F s x) (∫ x, phi x * F' t x) t := by
  let T := |t| + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨C, c, hC, hc, hbound⟩ := hb' T hT
  have hcont (s : ℝ) : Continuous (fun x => phi x * F s x) :=
    (continuous_phi d).mul (hF.comp (continuous_const.prodMk continuous_id))
  have hcont' (s : ℝ) : Continuous (fun x => phi x * F' s x) :=
    (continuous_phi d).mul (hF'.comp (continuous_const.prodMk continuous_id))
  have hint : Integrable (fun x => phi x * F t x) :=
    (hb T hT).gaussian_integrable ⟨t, by dsimp [T]; linarith⟩
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall t 1) (bound := fun x => C * (phi x * exp (c * ‖x‖)))
    (Metric.closedBall_mem_nhds t (by norm_num))
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable) hint
    (hcont' t).aestronglyMeasurable _
    ((integrable_phi_mul_exp_norm d c).const_mul C) _).2
  · filter_upwards [] with x s hs
    have hsT : |s| ≤ T := by
      have hdist : |s - t| ≤ 1 := by simpa [Real.dist_eq] using hs
      have htri := abs_add_le (s - t) t
      rw [sub_add_cancel] at htri
      dsimp [T]; linarith
    simp only [norm_mul, Real.norm_of_nonneg (phi_pos x).le]
    calc
      phi x * ‖F' s x‖ ≤ phi x * (C * exp (c * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (hbound ⟨s, hsT⟩ x) (phi_pos x).le
      _ = _ := by ring
  · exact Eventually.of_forall fun x s _ => (hd s x).const_mul (phi x)

end GaussianComparison.GaussianModel
