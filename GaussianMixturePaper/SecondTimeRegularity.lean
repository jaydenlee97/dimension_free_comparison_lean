import GaussianMixturePaper.FisherMatrix

/-! Local integrable bounds for the actual first and second time derivatives
of the three generator-density integrands in Section 3. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

/-- Uniform exponential growth on every bounded time interval. -/
def LocalExpGrowth {d : ℕ} (F : ℝ → Space d → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => F s.val x)

namespace LocalExpGrowth
variable {d : ℕ} {F G : ℝ → Space d → ℝ}
theorem const (a : ℝ) : LocalExpGrowth (fun _ (_ : Space d) => a) :=
  fun _ _ => ExpGrowth.const a
theorem add (hF : LocalExpGrowth F) (hG : LocalExpGrowth G) :
    LocalExpGrowth (fun t x => F t x + G t x) := fun T hT => (hF T hT).add (hG T hT)
theorem sub (hF : LocalExpGrowth F) (hG : LocalExpGrowth G) :
    LocalExpGrowth (fun t x => F t x - G t x) := fun T hT => (hF T hT).sub (hG T hT)
theorem neg (hF : LocalExpGrowth F) : LocalExpGrowth (fun t x => -F t x) :=
  fun T hT => (hF T hT).neg
theorem mul (hF : LocalExpGrowth F) (hG : LocalExpGrowth G) :
    LocalExpGrowth (fun t x => F t x * G t x) := fun T hT => (hF T hT).mul (hG T hT)
theorem pow (hF : LocalExpGrowth F) (n : ℕ) : LocalExpGrowth (fun t x => F t x ^ n) := by
  induction n with
  | zero => simpa using const (d := d) 1
  | succ n ih => simpa [pow_succ] using ih.mul hF
theorem sqrt (hF : LocalExpGrowth F) : LocalExpGrowth (fun t x => sqrt (F t x)) :=
  fun T hT => (hF T hT).sqrt
end LocalExpGrowth

/-- A twice differentiable family with continuous, exponentially bounded jets.
All derivative fields are proved to be derivatives rather than postulated when
constructing the Gaussian instances below. -/
structure TimeJet {d : ℕ} (F : ℝ → Space d → ℝ) where
  first : ℝ → Space d → ℝ
  second : ℝ → Space d → ℝ
  hasFirst : ∀ t x, HasDerivAt (fun s => F s x) (first t x) t
  hasSecond : ∀ t x, HasDerivAt (fun s => first s x) (second t x) t
  continuous : Continuous F.uncurry
  continuousFirst : Continuous first.uncurry
  continuousSecond : Continuous second.uncurry
  growth : LocalExpGrowth F
  growthFirst : LocalExpGrowth first
  growthSecond : LocalExpGrowth second

namespace TimeJet
variable {d : ℕ} {F G : ℝ → Space d → ℝ}

def const (a : ℝ) : TimeJet (fun _ (_ : Space d) => a) where
  first := fun _ _ => 0
  second := fun _ _ => 0
  hasFirst := fun t _ => hasDerivAt_const t a
  hasSecond := fun t _ => hasDerivAt_const t 0
  continuous := continuous_const
  continuousFirst := continuous_const
  continuousSecond := continuous_const
  growth := LocalExpGrowth.const a
  growthFirst := LocalExpGrowth.const 0
  growthSecond := LocalExpGrowth.const 0

def add (hF : TimeJet F) (hG : TimeJet G) : TimeJet (fun t x => F t x + G t x) where
  first := fun t x => hF.first t x + hG.first t x
  second := fun t x => hF.second t x + hG.second t x
  hasFirst := fun t x => (hF.hasFirst t x).add (hG.hasFirst t x)
  hasSecond := fun t x => (hF.hasSecond t x).add (hG.hasSecond t x)
  continuous := hF.continuous.add hG.continuous
  continuousFirst := hF.continuousFirst.add hG.continuousFirst
  continuousSecond := hF.continuousSecond.add hG.continuousSecond
  growth := hF.growth.add hG.growth
  growthFirst := hF.growthFirst.add hG.growthFirst
  growthSecond := hF.growthSecond.add hG.growthSecond

def sub (hF : TimeJet F) (hG : TimeJet G) : TimeJet (fun t x => F t x - G t x) where
  first := fun t x => hF.first t x - hG.first t x
  second := fun t x => hF.second t x - hG.second t x
  hasFirst := fun t x => (hF.hasFirst t x).sub (hG.hasFirst t x)
  hasSecond := fun t x => (hF.hasSecond t x).sub (hG.hasSecond t x)
  continuous := hF.continuous.sub hG.continuous
  continuousFirst := hF.continuousFirst.sub hG.continuousFirst
  continuousSecond := hF.continuousSecond.sub hG.continuousSecond
  growth := hF.growth.sub hG.growth
  growthFirst := hF.growthFirst.sub hG.growthFirst
  growthSecond := hF.growthSecond.sub hG.growthSecond

def mul (hF : TimeJet F) (hG : TimeJet G) : TimeJet (fun t x => F t x * G t x) where
  first := fun t x => hF.first t x * G t x + F t x * hG.first t x
  second := fun t x => hF.second t x * G t x + hF.first t x * hG.first t x +
    (hF.first t x * hG.first t x + F t x * hG.second t x)
  hasFirst := fun t x => (hF.hasFirst t x).mul (hG.hasFirst t x)
  hasSecond := fun t x => ((hF.hasSecond t x).mul (hG.hasFirst t x)).add
    ((hF.hasFirst t x).mul (hG.hasSecond t x))
  continuous := hF.continuous.mul hG.continuous
  continuousFirst := (hF.continuousFirst.mul hG.continuous).add
    (hF.continuous.mul hG.continuousFirst)
  continuousSecond := ((hF.continuousSecond.mul hG.continuous).add
    (hF.continuousFirst.mul hG.continuousFirst)).add
    ((hF.continuousFirst.mul hG.continuousFirst).add (hF.continuous.mul hG.continuousSecond))
  growth := hF.growth.mul hG.growth
  growthFirst := (hF.growthFirst.mul hG.growth).add (hF.growth.mul hG.growthFirst)
  growthSecond := ((hF.growthSecond.mul hG.growth).add
    (hF.growthFirst.mul hG.growthFirst)).add
    ((hF.growthFirst.mul hG.growthFirst).add (hF.growth.mul hG.growthSecond))

def inv (hF : TimeJet F) (hp : ∀ t x, F t x ≠ 0)
    (hi : LocalExpGrowth (fun t x => (F t x)⁻¹)) :
    TimeJet (fun t x => (F t x)⁻¹) where
  first := fun t x => -hF.first t x * (F t x)⁻¹ ^ 2
  second := fun t x => -hF.second t x * (F t x)⁻¹ ^ 2 +
    2 * hF.first t x ^ 2 * (F t x)⁻¹ ^ 3
  hasFirst := by
    intro t x
    convert! (hF.hasFirst t x).inv (hp t x) using 1
    field_simp
  hasSecond := by
    intro t x
    convert! ((hF.hasSecond t x).neg).mul (((hF.hasFirst t x).inv (hp t x)).pow 2) using 1
    simp only [Pi.inv_apply, Pi.pow_apply, Pi.neg_apply]
    field_simp [hp t x]
    linear_combination -2 * hF.first t x ^ 2 * (mul_inv_cancel₀ (hp t x))
  continuous := hF.continuous.inv₀ (fun p => hp p.1 p.2)
  continuousFirst := by
    convert! hF.continuousFirst.neg.mul
      ((hF.continuous.inv₀ (fun p => hp p.1 p.2)).pow 2) using 1
  continuousSecond := by
    convert! (hF.continuousSecond.neg.mul
      ((hF.continuous.inv₀ (fun p => hp p.1 p.2)).pow 2)).add
      (((continuous_const : Continuous (fun _ : ℝ × Space d => (2 : ℝ))).mul (hF.continuousFirst.pow 2)).mul
        ((hF.continuous.inv₀ (fun p => hp p.1 p.2)).pow 3)) using 1
  growth := hi
  growthFirst := hF.growthFirst.neg.mul (hi.pow 2)
  growthSecond := (hF.growthSecond.neg.mul (hi.pow 2)).add
    (((LocalExpGrowth.const 2).mul (hF.growthFirst.pow 2)).mul (hi.pow 3))

def log (hF : TimeJet F) (hp : ∀ t x, 0 < F t x)
    (hi : LocalExpGrowth (fun t x => (F t x)⁻¹)) :
    TimeJet (fun t x => Real.log (F t x)) where
  first := fun t x => hF.first t x * (F t x)⁻¹
  second := fun t x => hF.second t x * (F t x)⁻¹ - hF.first t x ^ 2 * (F t x)⁻¹ ^ 2
  hasFirst := by
    intro t x
    simpa only [div_eq_mul_inv] using (hF.hasFirst t x).log (hp t x).ne'
  hasSecond := by
    intro t x
    convert! (hF.hasSecond t x).mul ((hF.hasFirst t x).inv (hp t x).ne') using 1
    simp only [Pi.inv_apply]
    field_simp [(hp t x).ne']
    ring
  continuous := hF.continuous.log (fun p => (hp p.1 p.2).ne')
  continuousFirst := hF.continuousFirst.mul (hF.continuous.inv₀ (fun p => (hp p.1 p.2).ne'))
  continuousSecond := by
    convert! (hF.continuousSecond.mul (hF.continuous.inv₀ (fun p => (hp p.1 p.2).ne'))).sub
      ((hF.continuousFirst.pow 2).mul ((hF.continuous.inv₀ (fun p => (hp p.1 p.2).ne')).pow 2)) using 1
  growth := fun T hT => (hF.growth T hT).log (hi T hT) (fun t x => hp t.val x)
  growthFirst := hF.growthFirst.mul hi
  growthSecond := (hF.growthSecond.mul hi).sub ((hF.growthFirst.pow 2).mul (hi.pow 2))

def sqrt (hF : TimeJet F) (hp : ∀ t x, 0 < F t x)
    (hi : LocalExpGrowth (fun t x => (F t x)⁻¹)) :
    TimeJet (fun t x => Real.sqrt (F t x)) := by
  have hsi : LocalExpGrowth (fun t x => (Real.sqrt (F t x))⁻¹) := by
    simpa only [Real.sqrt_inv] using hi.sqrt
  refine {
    first := fun t x => hF.first t x * (Real.sqrt (F t x))⁻¹ / 2
    second := fun t x => hF.second t x * (Real.sqrt (F t x))⁻¹ / 2 -
      hF.first t x ^ 2 * (Real.sqrt (F t x))⁻¹ ^ 3 / 4
    hasFirst := ?_
    hasSecond := ?_
    continuous := hF.continuous.sqrt
    continuousFirst := (hF.continuousFirst.mul
      (hF.continuous.sqrt.inv₀ (fun p => (Real.sqrt_pos.mpr (hp p.1 p.2)).ne'))).div_const 2
    continuousSecond := by
      convert! ((hF.continuousSecond.mul
        (hF.continuous.sqrt.inv₀ (fun p => (Real.sqrt_pos.mpr (hp p.1 p.2)).ne'))).div_const 2).sub
        (((hF.continuousFirst.pow 2).mul
          ((hF.continuous.sqrt.inv₀ (fun p => (Real.sqrt_pos.mpr (hp p.1 p.2)).ne')).pow 3)).div_const 4) using 1
    growth := hF.growth.sqrt
    growthFirst := ?_
    growthSecond := ?_ }
  · intro t x
    convert! (hF.hasFirst t x).sqrt (hp t x).ne' using 1
    field_simp
  · intro t x
    convert! ((hF.hasSecond t x).mul
      (((hF.hasFirst t x).sqrt (hp t x).ne').inv (Real.sqrt_pos.mpr (hp t x)).ne')).div_const 2 using 1
    simp only [Pi.inv_apply]
    field_simp [(Real.sqrt_pos.mpr (hp t x)).ne']
    ring
  · simpa only [div_eq_mul_inv] using (hF.growthFirst.mul hsi).mul (LocalExpGrowth.const (2 : ℝ)⁻¹)
  · simpa only [div_eq_mul_inv] using
      ((hF.growthSecond.mul hsi).mul (LocalExpGrowth.const (2 : ℝ)⁻¹)).sub
      (((hF.growthFirst.pow 2).mul (hsi.pow 3)).mul (LocalExpGrowth.const (4 : ℝ)⁻¹))

/-- The first and second fields coincide with the actual derivative operators. -/
theorem deriv_eq (hF : TimeJet F) (t : ℝ) (x : Space d) :
    deriv (fun s => F s x) t = hF.first t x := (hF.hasFirst t x).deriv

theorem second_deriv_eq (hF : TimeJet F) (t : ℝ) (x : Space d) :
    deriv (deriv (fun s => F s x)) t = hF.second t x := by
  have he : deriv (fun s => F s x) = fun s => hF.first s x := funext fun s => hF.deriv_eq s x
  rw [he]
  exact (hF.hasSecond t x).deriv

theorem contDiff_two (hF : TimeJet F) (x : Space d) : ContDiff ℝ 2 (fun t => F t x) := by
  have hfirst : ContDiff ℝ 1 (fun t => hF.first t x) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun t => (hF.hasSecond t x).differentiableAt, ?_⟩
    have he : deriv (fun t => hF.first t x) = fun t => hF.second t x :=
      funext fun t => (hF.hasSecond t x).deriv
    rw [he]
    exact hF.continuousSecond.comp (continuous_id.prodMk continuous_const)
  change ContDiff ℝ (1 + 1) (fun t => F t x)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (hF.hasFirst t x).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · have he : deriv (fun t => F t x) = fun t => hF.first t x :=
      funext fun t => (hF.hasFirst t x).deriv
    rw [he]
    exact hfirst


end TimeJet

/-- The actual second time derivative of the partition integral. -/
def scaledPartitionDDot {d : ℕ} {M : ℝ} (μ : Measure (Ball d M)) (s : ℝ) (x : Space d) :=
  ∫ θ, ((⟪θ.val, x⟫_ℝ - s * ‖θ.val‖ ^ 2) ^ 2 - ‖θ.val‖ ^ 2) *
    kernel θ.val (s • x) (s ^ 2) ∂μ

theorem scaledPartitionDot_hasDerivAt {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] (s : ℝ) (x : Space d) :
    HasDerivAt (fun r => scaledPartitionDot μ r x) (scaledPartitionDDot μ s x) s := by
  unfold scaledPartitionDot scaledPartitionDDot
  refine hasDerivAt_integral_compact_prior μ
    (F := fun r θ => (⟪θ.val, x⟫_ℝ - r * ‖θ.val‖ ^ 2) * kernel θ.val (r • x) (r ^ 2))
    (F' := fun r θ => ((⟪θ.val, x⟫_ℝ - r * ‖θ.val‖ ^ 2) ^ 2 - ‖θ.val‖ ^ 2) *
      kernel θ.val (r • x) (r ^ 2))
    ?_ ?_ ?_ s
  · unfold Function.uncurry kernel; fun_prop
  · unfold Function.uncurry kernel; fun_prop
  · intro r θ
    have hk : HasDerivAt (fun u => kernel θ.val (u • x) (u ^ 2))
        ((⟪θ.val, x⟫_ℝ - r * ‖θ.val‖ ^ 2) * kernel θ.val (r • x) (r ^ 2)) r := by
      convert! (((hasDerivAt_id r).mul_const ⟪θ.val, x⟫_ℝ).sub
        ((((hasDerivAt_id r).pow 2).mul_const (‖θ.val‖ ^ 2)).div_const 2)).exp using 1
      · funext u; simp [kernel, real_inner_smul_right]
      · dsimp [kernel]; rw [real_inner_smul_right]; ring
    convert! ((hasDerivAt_const r ⟪θ.val, x⟫_ℝ).sub
      ((hasDerivAt_id r).mul_const (‖θ.val‖ ^ 2))).mul hk using 1
    simp only [id_eq, Pi.sub_apply]
    ring

theorem continuous_scaledPartitionDDot {d : ℕ} {M : ℝ}
    (μ : Measure (Ball d M)) [IsFiniteMeasure μ] : Continuous (scaledPartitionDDot μ).uncurry := by
  have hc : Continuous (fun p : (ℝ × Space d) × Ball d M =>
      ((⟪p.2.val, p.1.2⟫_ℝ - p.1.1 * ‖p.2.val‖ ^ 2) ^ 2 - ‖p.2.val‖ ^ 2) *
      kernel p.2.val (p.1.1 • p.1.2) (p.1.1 ^ 2)) := by unfold kernel; fun_prop
  change Continuous (fun p : ℝ × Space d => ∫ θ : Ball d M,
    ((⟪θ.val, p.2⟫_ℝ - p.1 * ‖θ.val‖ ^ 2) ^ 2 - ‖θ.val‖ ^ 2) *
      kernel θ.val (p.1 • p.2) (p.1 ^ 2) ∂μ)
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ

theorem scaledPartitionDDot_growth {d : ℕ} {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] :
    ExpGrowth (fun (s : {s : ℝ // |s| ≤ T}) x => scaledPartitionDDot μ s.val x) := by
  have hw := scaledWeight_growth (d := d) hM hT
  have hn : ExpGrowth (fun (a : {s : ℝ // |s| ≤ T} × Ball d M) (_ : Space d) => ‖a.2.val‖ ^ 2) := by
    apply ExpGrowth.of_bounded (M ^ 2) (sq_nonneg M)
    intro a x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [a.2.property, norm_nonneg a.2.val]
  simpa only [scaledPartitionDDot, pow_two] using
    (((hw.mul hw).sub hn).mul (scaledKernel_growth hM hT)).integral (μ := μ)

def partitionTimeJet {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ : Measure (Ball d M)) [IsProbabilityMeasure μ] : TimeJet (scaledPartition μ) where
  first := scaledPartitionDot μ
  second := scaledPartitionDDot μ
  hasFirst := scaledPartition_hasDerivAt μ
  hasSecond := scaledPartitionDot_hasDerivAt μ
  continuous := continuous_scaledPartition μ
  continuousFirst := continuous_scaledPartitionDot μ
  continuousSecond := continuous_scaledPartitionDDot μ
  growth := fun _ hT => scaledPartition_growth hM hT μ
  growthFirst := fun _ hT => scaledPartitionDot_growth hM hT μ
  growthSecond := fun _ hT => scaledPartitionDDot_growth hM hT μ

/-- Remove the common Gaussian factor from a generator-density integrand. -/
def scaledGeneratorIntegrand {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M))
    (f : ℝ → ℝ) (t : ℝ) (x : Space d) : ℝ :=
  scaledPartition ν t x * f (scaledPartition μ t x / scaledPartition ν t x)

theorem generator_integrand_factorization {d : ℕ} {M : ℝ}
    (μ ν : Measure (Ball d M)) (f : ℝ → ℝ) (t : ℝ) (x : Space d) :
    meanScaledDensity ν t x * f (meanScaledDensity μ t x / meanScaledDensity ν t x) =
      phi x * scaledGeneratorIntegrand μ ν f t x := by
  rw [density_ratio_eq_scaledRatio μ ν, meanScaledDensity_eq_partition]
  unfold scaledGeneratorIntegrand scaledRatio scaledPartition
  ring

theorem generatorTimeJet {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : ℝ → ℝ) (hf : IsPaperGenerator f) : Nonempty (TimeJet (scaledGeneratorIntegrand μ ν f)) := by
  have hP := partitionTimeJet hM μ
  have hQ := partitionTimeJet hM ν
  have hiP : LocalExpGrowth (fun t x => (scaledPartition μ t x)⁻¹) :=
    fun _ hT => scaledPartition_inv_growth hM hT μ
  have hiQ : LocalExpGrowth (fun t x => (scaledPartition ν t x)⁻¹) :=
    fun _ hT => scaledPartition_inv_growth hM hT ν
  have hR : TimeJet (fun t x => scaledPartition μ t x / scaledPartition ν t x) := by
    simpa only [div_eq_mul_inv] using hP.mul (hQ.inv (fun t x => (scaledPartition_pos hM ν t x).ne') hiQ)
  have hRpos : ∀ t x, 0 < scaledPartition μ t x / scaledPartition ν t x :=
    fun t x => div_pos (scaledPartition_pos hM μ t x) (scaledPartition_pos hM ν t x)
  have hiR : LocalExpGrowth (fun t x => (scaledPartition μ t x / scaledPartition ν t x)⁻¹) := by
    have he : (fun t x => (scaledPartition μ t x / scaledPartition ν t x)⁻¹) =
        (fun t x => scaledPartition ν t x * (scaledPartition μ t x)⁻¹) := by
      funext t x; rw [inv_div, div_eq_mul_inv]
    rw [he]
    exact hQ.growth.mul hiP
  obtain rfl | rfl | rfl := hf
  · exact ⟨hQ.mul (((hR.mul (hR.log hRpos hiR)).sub hR).add (TimeJet.const 1))⟩
  · let hS := (hR.sqrt hRpos hiR).sub (TimeJet.const 1)
    constructor
    change TimeJet (fun t x => scaledPartition ν t x * ((sqrt (scaledPartition μ t x / scaledPartition ν t x) - 1) ^ 2))
    simpa only [pow_two] using hQ.mul (hS.mul hS)
  · let hS := hR.sub (TimeJet.const 1)
    constructor
    change TimeJet (fun t x => scaledPartition ν t x * ((scaledPartition μ t x / scaledPartition ν t x - 1) ^ 2))
    simpa only [pow_two] using hQ.mul (hS.mul hS)

/-- The generator-density function before integrating over space. -/
def paperGeneratorDensity {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M))
    (f : ℝ → ℝ) (t : ℝ) (x : Space d) : ℝ :=
  meanScaledDensity ν t x * f (meanScaledDensity μ t x / meanScaledDensity ν t x)

variable {d : ℕ} {M : ℝ}
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Each actual generator-density function is twice continuously differentiable
in time at every spatial point. -/
theorem paperGeneratorDensity_contDiff_two (hM : 0 ≤ M) (f : ℝ → ℝ) (hf : IsPaperGenerator f) (x : Space d) :
    ContDiff ℝ 2 (fun t => paperGeneratorDensity μ ν f t x) := by
  obtain ⟨J⟩ := generatorTimeJet hM μ ν f hf
  have he : (fun t => paperGeneratorDensity μ ν f t x) =
      (fun t => phi x * scaledGeneratorIntegrand μ ν f t x) :=
    funext fun t => generator_integrand_factorization μ ν f t x
  rw [he]
  exact contDiff_const.mul (J.contDiff_two x)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem paperGeneratorDensity_first_eq (f : ℝ → ℝ)
    (J : TimeJet (scaledGeneratorIntegrand μ ν f)) (t : ℝ) (x : Space d) :
    deriv (fun s => paperGeneratorDensity μ ν f s x) t = phi x * J.first t x := by
  have he : (fun s => paperGeneratorDensity μ ν f s x) =
      (fun s => phi x * scaledGeneratorIntegrand μ ν f s x) :=
    funext fun s => generator_integrand_factorization μ ν f s x
  rw [he]
  exact ((J.hasFirst t x).const_mul (phi x)).deriv

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
private theorem paperGeneratorDensity_second_eq (f : ℝ → ℝ)
    (J : TimeJet (scaledGeneratorIntegrand μ ν f)) (t : ℝ) (x : Space d) :
    deriv (deriv (fun s => paperGeneratorDensity μ ν f s x)) t = phi x * J.second t x := by
  have he : deriv (fun s => paperGeneratorDensity μ ν f s x) =
      (fun s => phi x * J.first s x) := funext fun s => paperGeneratorDensity_first_eq μ ν f J s x
  rw [he]
  exact ((J.hasSecond t x).const_mul (phi x)).deriv

/-- Section 3(i): both actual time derivatives are absolutely integrable in
space, at every real interpolation parameter. -/
theorem paperGeneratorDensity_time_derivatives_integrable (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : IsPaperGenerator f) (t : ℝ) :
    Integrable (fun x => deriv (fun s => paperGeneratorDensity μ ν f s x) t) ∧
    Integrable (fun x => deriv (deriv (fun s => paperGeneratorDensity μ ν f s x)) t) := by
  obtain ⟨J⟩ := generatorTimeJet hM μ ν f hf
  simp_rw [paperGeneratorDensity_first_eq μ ν f J,
    paperGeneratorDensity_second_eq μ ν f J]
  exact ⟨(fixed_growth t J.growthFirst).gaussian_integrable ()
      (J.continuousFirst.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable,
    (fixed_growth t J.growthSecond).gaussian_integrable ()
      (J.continuousSecond.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable⟩

/-- Uniform local Gaussian domination of the first and second time derivatives.
This supplies an integrable envelope on every bounded time interval, which is
stronger than pointwise-in-time integrability. -/
theorem paperGeneratorDensity_time_derivatives_local_envelope (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : IsPaperGenerator f) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧
      Integrable (fun x : Space d => C * (phi x * exp (c * ‖x‖))) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ x : Space d,
        |deriv (fun s => paperGeneratorDensity μ ν f s x) t| +
          |deriv (deriv (fun s => paperGeneratorDensity μ ν f s x)) t| ≤
          C * (phi x * exp (c * ‖x‖)) := by
  obtain ⟨J⟩ := generatorTimeJet hM μ ν f hf
  obtain ⟨C, c, hC, hc, hb⟩ :=
    ((J.growthFirst T hT).norm.add (J.growthSecond T hT).norm)
  refine ⟨C, c, hC, hc, (integrable_phi_mul_exp_norm d c).const_mul C, ?_⟩
  intro t ht x
  rw [paperGeneratorDensity_first_eq μ ν f J, paperGeneratorDensity_second_eq μ ν f J,
    abs_mul, abs_mul, abs_of_pos (phi_pos x)]
  have hb' := hb ⟨t, ht⟩ x
  simp only [Real.norm_eq_abs] at hb'
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (J.first t x)) (abs_nonneg (J.second t x)))] at hb'
  calc
    phi x * |J.first t x| + phi x * |J.second t x| =
        phi x * (|J.first t x| + |J.second t x|) := by ring
    _ ≤ phi x * (C * exp (c * ‖x‖)) := mul_le_mul_of_nonneg_left hb' (phi_pos x).le
    _ = _ := by ring


end GaussianComparison.GaussianModel
