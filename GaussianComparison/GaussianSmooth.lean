import GaussianComparison.GaussianRegularity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Joint smoothness of the Gaussian partition integral

This proves the full joint smoothness asserted in Lemma 4.1 of the manuscript.
The proof differentiates the actual compact-prior Bochner integral and inducts
over the regularity order, allowing Banach-valued continuous prior weights.
All domination needed to interchange differentiation and integration is proved
from compactness; no smoothness or interchange assumption is introduced.
-/

noncomputable section

open MeasureTheory Real Filter
open scoped Topology InnerProductSpace ContDiff

namespace GaussianComparison.GaussianModel

universe u

instance ballSecondCountableTopology (d : ℕ) (M : ℝ) : SecondCountableTopology (Ball d M) :=
  inferInstanceAs (SecondCountableTopology {θ : Space d // ‖θ‖ ≤ M})

/-- The linear exponent of the kernel, as a map in space and time jointly. -/
def jointExponent {d : ℕ} (θ : Space d) : (Space d × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ θ).comp (ContinuousLinearMap.fst ℝ (Space d) ℝ) -
    (‖θ‖ ^ 2 / 2) • ContinuousLinearMap.snd ℝ (Space d) ℝ

theorem jointExponent_apply {d : ℕ} (θ : Space d) (p : Space d × ℝ) :
    jointExponent θ p = ⟪θ, p.1⟫_ℝ - p.2 * ‖θ‖ ^ 2 / 2 := by
  simp [jointExponent]
  ring

theorem continuous_jointExponent {d : ℕ} :
    Continuous (jointExponent : Space d → (Space d × ℝ) →L[ℝ] ℝ) := by
  unfold jointExponent
  fun_prop

/-- Compact-prior Fréchet differentiation for arbitrary complete target spaces. -/
theorem hasFDerivAt_integral_compact_prior_joint
    {d : ℕ} {M : ℝ} {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    {F : (Space d × ℝ) → Ball d M → E}
    {F' : (Space d × ℝ) → Ball d M → (Space d × ℝ) →L[ℝ] E}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ y θ, HasFDerivAt (fun z => F z θ) (F' y θ) y)
    (x : Space d × ℝ) :
    HasFDerivAt (fun y => ∫ θ, F y θ ∂μ) (∫ θ, F' x θ ∂μ) x := by
  have hFy (y : Space d × ℝ) : Continuous (F y) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hF'y (y : Space d × ℝ) : Continuous (F' y) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  have hint : Integrable (F x) μ := by
    simpa using (hFy x).continuousOn.integrableOn_compact isCompact_univ
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall x 1).prod (isCompact_univ (X := Ball d M))).bddAbove_image
      hF'.norm.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x (by norm_num))
    (Filter.Eventually.of_forall fun y => (hFy y).aestronglyMeasurable) hint
    (hF'y x).aestronglyMeasurable _ (integrable_const C) _
  · exact Filter.Eventually.of_forall fun θ y hy =>
      hC (Set.mem_image_of_mem
        (fun q : (Space d × ℝ) × Ball d M => ‖F' q.1 q.2‖)
        (show (y, θ) ∈ Metric.closedBall x 1 ×ˢ Set.univ from ⟨hy, Set.mem_univ θ⟩))
  · exact Filter.Eventually.of_forall fun θ y _ => hd y θ

/-- Joint derivative of a continuously weighted partition integral. -/
theorem weightedPartition_hasFDerivAt_joint
    {d : ℕ} {M : ℝ} {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    (w : Ball d M → E) (hw : Continuous w) (p : Space d × ℝ) :
    HasFDerivAt (fun q : Space d × ℝ => ∫ θ, kernel θ.val q.1 q.2 • w θ ∂μ)
      (∫ θ, kernel θ.val p.1 p.2 • (jointExponent θ.val).smulRight (w θ) ∂μ) p := by
  have hL : Continuous (fun θ : Ball d M => (jointExponent θ.val).smulRight (w θ)) := by
    exact (ContinuousLinearMap.smulRightL ℝ (Space d × ℝ) E).continuous.comp
      (continuous_jointExponent.comp continuous_subtype_val) |>.clm_apply hw
  refine hasFDerivAt_integral_compact_prior_joint μ
    (F := fun q θ => kernel θ.val q.1 q.2 • w θ)
    (F' := fun q θ => kernel θ.val q.1 q.2 • (jointExponent θ.val).smulRight (w θ))
    ?_ ?_ ?_ p
  · unfold Function.uncurry kernel
    fun_prop
  · have hK : Continuous (fun q : (Space d × ℝ) × Ball d M =>
        kernel q.2.val q.1.1 q.1.2) := by
      unfold kernel
      fun_prop
    exact hK.smul (hL.comp continuous_snd)
  · intro q θ
    have h := ((jointExponent θ.val).hasFDerivAt (x := q)).exp.smul_const (w θ)
    convert! h using 1
    · ext z
      rw [kernel, jointExponent_apply]
    · apply ContinuousLinearMap.ext
      intro z
      simp [jointExponent_apply, kernel, smul_smul]

/-- Every finite joint regularity order, for arbitrary continuous prior weights. -/
theorem weightedPartition_contDiff_joint_nat
    {d : ℕ} {M : ℝ} (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    (n : ℕ) {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : Ball d M → E) (hw : Continuous w) :
    ContDiff ℝ n (fun p : Space d × ℝ => ∫ θ, kernel θ.val p.1 p.2 • w θ ∂μ) := by
  induction n generalizing E with
  | zero =>
      apply contDiff_zero.mpr
      have hc : Continuous (fun q : (Space d × ℝ) × Ball d M =>
          kernel q.2.val q.1.1 q.1.2 • w q.2) := by
        unfold kernel
        fun_prop
      simpa using continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ
  | succ n ih =>
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun p => ∫ θ,
        kernel θ.val p.1 p.2 • (jointExponent θ.val).smulRight (w θ) ∂μ, ?_, ?_⟩
      · apply ih
        exact (ContinuousLinearMap.smulRightL ℝ (Space d × ℝ) E).continuous.comp
          (continuous_jointExponent.comp continuous_subtype_val) |>.clm_apply hw
      · exact weightedPartition_hasFDerivAt_joint μ w hw

/-- Full joint C-infinity regularity, proved for the actual weighted integral. -/
theorem weightedPartition_contDiff_joint
    {d : ℕ} {M : ℝ} {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ]
    (w : Ball d M → E) (hw : Continuous w) :
    ContDiff ℝ ∞ (fun p : Space d × ℝ => ∫ θ, kernel θ.val p.1 p.2 • w θ ∂μ) := by
  exact contDiff_infty.mpr fun n => weightedPartition_contDiff_joint_nat μ n w hw

/-- Lemma 4.1: the actual partition function is jointly C-infinity. -/
theorem partition_contDiff_joint {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    ContDiff ℝ ∞ (fun p : Space d × ℝ => partition μ p.1 p.2) := by
  simpa [partition] using weightedPartition_contDiff_joint μ (fun _ => (1 : ℝ)) continuous_const

/-- Lemma 4.1: positivity and composition give joint C-infinity regularity of log Z. -/
theorem log_partition_contDiff_joint {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    ContDiff ℝ ∞ (fun p : Space d × ℝ => log (partition μ p.1 p.2)) :=
  (partition_contDiff_joint μ).log fun p => (partition_pos hM μ p.1 p.2).ne'

/-- The posterior mean used as the stochastic drift is jointly smooth as well. -/
theorem posteriorMean_contDiff_joint {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    ContDiff ℝ ∞ (fun p : Space d × ℝ => posteriorMean μ p.1 p.2) := by
  exact ((partition_contDiff_joint μ).inv
    (fun p => (partition_pos hM μ p.1 p.2).ne')).smul
      (weightedPartition_contDiff_joint μ (fun θ => θ.val) continuous_subtype_val)

/-- Joint C2 is a convenient stronger input than separate C1-in-time and C2-in-space. -/
theorem partition_contDiff_joint_two {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    ContDiff ℝ 2 (fun p : Space d × ℝ => partition μ p.1 p.2) :=
  (partition_contDiff_joint μ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

theorem log_partition_contDiff_joint_two {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    ContDiff ℝ 2 (fun p : Space d × ℝ => log (partition μ p.1 p.2)) :=
  (log_partition_contDiff_joint hM μ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- The full joint derivative is continuous at every finite order. -/
theorem partition_continuous_iteratedFDeriv_joint {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (n : ℕ) :
    Continuous (iteratedFDeriv ℝ n (fun p : Space d × ℝ => partition μ p.1 p.2)) := by
  exact (partition_contDiff_joint μ).continuous_iteratedFDeriv
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

/-- The complete Fréchet derivative hierarchy also exists for log Z. -/
theorem log_partition_continuous_iteratedFDeriv_joint {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (n : ℕ) :
    Continuous (iteratedFDeriv ℝ n (fun p : Space d × ℝ => log (partition μ p.1 p.2))) := by
  exact (log_partition_contDiff_joint hM μ).continuous_iteratedFDeriv
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

/-- A precise joint C1-in-time, C2-in-space package.  All derivatives below are
actual derivatives; continuity is joint in the space and time variables. -/
structure JointC12 {d : ℕ} (f : Space d × ℝ → ℝ) : Prop where
  continuous : Continuous f
  time_differentiable : ∀ p : Space d × ℝ,
    DifferentiableAt ℝ (fun t => f (p.1, t)) p.2
  space_differentiable : ∀ p : Space d × ℝ,
    DifferentiableAt ℝ (fun x => f (x, p.2)) p.1
  space_derivative_differentiable : ∀ p : Space d × ℝ,
    DifferentiableAt ℝ (fun x => fderiv ℝ (fun y => f (y, p.2)) x) p.1
  continuous_time_derivative : Continuous
    (fun p : Space d × ℝ => deriv (fun t => f (p.1, t)) p.2)
  continuous_space_derivative : Continuous
    (fun p : Space d × ℝ => fderiv ℝ (fun x => f (x, p.2)) p.1)
  continuous_space_second_derivative : Continuous
    (fun p : Space d × ℝ =>
      fderiv ℝ (fun x => fderiv ℝ (fun y => f (y, p.2)) x) p.1)

/-- Smooth functions supply all the jointly continuous derivatives used by Itô's lemma. -/
theorem jointC12_of_contDiff {d : ℕ} {f : Space d × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) : JointC12 f := by
  have ht : ContDiff ℝ ∞ (fun p : Space d × ℝ =>
      fderiv ℝ (fun t => f (p.1, t)) p.2) := by
    have hh : ContDiff ℝ ∞
        (Function.uncurry (fun p : Space d × ℝ => fun t : ℝ => f (p.1, t))) :=
      hf.comp ((contDiff_fst.fst).prodMk contDiff_snd)
    exact hh.fderiv contDiff_snd (by simp)
  have hx : ContDiff ℝ ∞ (fun p : Space d × ℝ =>
      fderiv ℝ (fun x => f (x, p.2)) p.1) := by
    have hh : ContDiff ℝ ∞
        (Function.uncurry (fun p : Space d × ℝ => fun x : Space d => f (x, p.2))) :=
      hf.comp (contDiff_snd.prodMk (contDiff_fst.snd))
    exact hh.fderiv contDiff_fst (by simp)
  have hxx : ContDiff ℝ ∞ (fun p : Space d × ℝ =>
      fderiv ℝ (fun x => fderiv ℝ (fun y => f (y, p.2)) x) p.1) := by
    have hh : ContDiff ℝ ∞
        (Function.uncurry (fun p : Space d × ℝ => fun x : Space d =>
          fderiv ℝ (fun y => f (y, p.2)) x)) :=
      hx.comp (contDiff_snd.prodMk (contDiff_fst.snd))
    exact hh.fderiv contDiff_fst (by simp)
  refine ⟨hf.continuous, ?_, ?_, ?_, ?_, hx.continuous, hxx.continuous⟩
  · intro p
    exact (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) p.2
  · intro p
    exact (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1
  · intro p
    exact (hx.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1
  · exact (ht.clm_apply contDiff_const).continuous

/-- The partition function satisfies the packaged joint C1,2 hypotheses. -/
theorem partition_jointC12 {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    JointC12 (fun p : Space d × ℝ => partition μ p.1 p.2) :=
  jointC12_of_contDiff (partition_contDiff_joint μ)

/-- The log partition function satisfies the packaged joint C1,2 hypotheses. -/
theorem log_partition_jointC12 {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    JointC12 (fun p : Space d × ℝ => log (partition μ p.1 p.2)) :=
  jointC12_of_contDiff (log_partition_contDiff_joint hM μ)

end GaussianComparison.GaussianModel
