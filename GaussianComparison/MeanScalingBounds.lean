import GaussianComparison.MeanScaling
import GaussianComparison.ExponentialGrowth

noncomputable section
open MeasureTheory Real Filter
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

def scaledPartition {d : ℕ} {M : ℝ} (μ : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  partition μ (s • x) (s ^ 2)

def scaledPartitionDot {d : ℕ} {M : ℝ} (μ : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  ∫ θ, (⟪θ.val, x⟫_ℝ - s * ‖θ.val‖ ^ 2) * kernel θ.val (s • x) (s ^ 2) ∂μ

def scaledLogRatio {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  log (scaledPartition μ s x / scaledPartition ν s x)

def scaledRatio {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  scaledPartition μ s x / scaledPartition ν s x

def scaledRootRatio {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  sqrt (scaledRatio μ ν s x)

theorem scaledPartition_pos {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] (s : ℝ) (x : Space d) :
    0 < scaledPartition μ s x := partition_pos hM μ _ _

theorem scaledPartition_hasDerivAt {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (s : ℝ) (x : Space d) :
    HasDerivAt (fun r => scaledPartition μ r x) (scaledPartitionDot μ s x) s := by
  unfold scaledPartition scaledPartitionDot partition
  refine hasDerivAt_integral_compact_prior μ
    (F := fun r θ => kernel θ.val (r • x) (r ^ 2))
    (F' := fun r θ => (⟪θ.val, x⟫_ℝ - r * ‖θ.val‖ ^ 2) * kernel θ.val (r • x) (r ^ 2))
    ?_ ?_ ?_ s
  · unfold Function.uncurry kernel; fun_prop
  · unfold Function.uncurry kernel; fun_prop
  · intro r θ
    convert! (((hasDerivAt_id r).mul_const ⟪θ.val, x⟫_ℝ).sub
      ((((hasDerivAt_id r).pow 2).mul_const (‖θ.val‖ ^ 2)).div_const 2)).exp using 1
    · funext u; simp [kernel, real_inner_smul_right]
    · dsimp [kernel]; rw [real_inner_smul_right]; ring

theorem continuous_scaledPartition {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    Continuous (Function.uncurry (scaledPartition μ)) := by
  exact Continuous.comp (g := fun p : Space d × ℝ => partition μ p.1 p.2)
    (f := fun p : ℝ × Space d => (p.1 • p.2, p.1 ^ 2)) (continuous_partition μ)
    ((continuous_fst.smul continuous_snd).prodMk (continuous_fst.pow 2))

theorem continuous_scaledPartitionDot {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] :
    Continuous (Function.uncurry (scaledPartitionDot μ)) := by
  have hc : Continuous (fun p : (ℝ × Space d) × Ball d M =>
      (⟪p.2.val, p.1.2⟫_ℝ - p.1.1 * ‖p.2.val‖ ^ 2) *
        kernel p.2.val (p.1.1 • p.1.2) (p.1.1 ^ 2)) := by
    unfold kernel; fun_prop
  change Continuous (fun p : ℝ × Space d => ∫ θ : Ball d M,
    (⟪θ.val, p.2⟫_ℝ - p.1 * ‖θ.val‖ ^ 2) * kernel θ.val (p.1 • p.2) (p.1 ^ 2) ∂μ)
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ

theorem scaledKernel_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ExpGrowth (fun (a : {s : ℝ // |s| ≤ T} × Ball d M) x =>
      kernel a.2.val (a.1.val • x) (a.1.val ^ 2)) := by
  refine ⟨1, T * M, by norm_num, by positivity, fun a x => ?_⟩
  rw [Real.norm_of_nonneg (kernel_pos _ _ _).le, one_mul]
  apply exp_le_exp.mpr
  have hi := abs_real_inner_le_norm a.2.val x
  have hs := a.1.property
  have hθ := a.2.property
  have hi' : |a.1.val * ⟪a.2.val, x⟫_ℝ| ≤ T * M * ‖x‖ := by
    rw [abs_mul]
    calc
      |a.1.val| * |⟪a.2.val, x⟫_ℝ| ≤ T * (M * ‖x‖) :=
        mul_le_mul hs (hi.trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _)))
          (abs_nonneg _) hT
      _ = _ := by ring
  rw [real_inner_smul_right]
  nlinarith [le_abs_self (a.1.val * ⟪a.2.val, x⟫_ℝ), sq_nonneg a.1.val,
    sq_nonneg ‖a.2.val‖]

theorem scaledWeight_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ExpGrowth (fun (a : {s : ℝ // |s| ≤ T} × Ball d M) (x : Space d) =>
      ⟪a.2.val, x⟫_ℝ - a.1.val * ‖a.2.val‖ ^ 2) := by
  apply (((ExpGrowth.const (A := {s : ℝ // |s| ≤ T} × Ball d M) M).mul
    ExpGrowth.radius).add (ExpGrowth.const (T * M ^ 2))).mono
  intro a x
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ M * ‖x‖ + T * M ^ 2)]
  have hsq : ‖a.2.val‖ ^ 2 ≤ M ^ 2 := by nlinarith [a.2.property, norm_nonneg a.2.val]
  calc
    |⟪a.2.val, x⟫_ℝ - a.1.val * ‖a.2.val‖ ^ 2| ≤
        |⟪a.2.val, x⟫_ℝ| + |a.1.val * ‖a.2.val‖ ^ 2| := abs_sub _ _
    _ ≤ M * ‖x‖ + T * M ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖a.2.val‖)]
      exact add_le_add ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right a.2.property (norm_nonneg _)))
        (mul_le_mul a.1.property hsq (sq_nonneg _) hT)

theorem scaledPartition_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledPartition μ s.val x) :=
  (scaledKernel_growth hM hT).integral

theorem scaledPartitionDot_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledPartitionDot μ s.val x) :=
  ((scaledWeight_growth hM hT).mul (scaledKernel_growth hM hT)).integral

theorem scaledPartition_inv_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => (scaledPartition μ s.val x)⁻¹) := by
  refine ⟨exp (T ^ 2 * M ^ 2 / 2), T * M, (exp_pos _).le, by positivity, fun s x => ?_⟩
  rw [Real.norm_of_nonneg (inv_pos.mpr (scaledPartition_pos hM μ s.val x)).le]
  have hl := (partition_bounds hM μ (s.val • x) (sq_nonneg s.val)).1
  have hs : s.val ^ 2 ≤ T ^ 2 := by
    nlinarith [sq_abs s.val, s.property, abs_nonneg s.val]
  have hn : ‖s.val • x‖ ≤ T * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right s.property (norm_nonneg _)
  have hl' : exp (-T * M * ‖x‖ - T ^ 2 * M ^ 2 / 2) ≤ scaledPartition μ s.val x := by
    apply le_trans _ hl
    apply exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hn hM
    have h2 := mul_le_mul_of_nonneg_right hs (sq_nonneg M)
    nlinarith
  calc
    (scaledPartition μ s.val x)⁻¹ ≤ (exp (-T * M * ‖x‖ - T ^ 2 * M ^ 2 / 2))⁻¹ :=
      inv_anti₀ (exp_pos _) hl'
    _ = _ := by rw [← exp_neg, ← exp_add]; congr 1; ring

theorem scaledRatio_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledRatio μ ν s.val x) := by
  simpa [scaledRatio, div_eq_mul_inv] using
    (scaledPartition_growth hM hT μ).mul (scaledPartition_inv_growth hM hT ν)

theorem scaledLogRatio_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledLogRatio μ ν s.val x) := by
  apply (scaledRatio_growth hM hT μ ν).log
  · simpa [scaledRatio, inv_div] using scaledRatio_growth hM hT ν μ
  · intro s x; exact div_pos (scaledPartition_pos hM μ _ _) (scaledPartition_pos hM ν _ _)

theorem scaledRootRatio_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledRootRatio μ ν s.val x) :=
  (scaledRatio_growth hM hT μ ν).sqrt

end GaussianComparison.GaussianModel
