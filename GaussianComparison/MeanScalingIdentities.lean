import GaussianComparison.MeanScalingDivergenceCalculus

/-! Elementary entropy and Hellinger dissipation identities, obtained by
testing the proved continuity equation. -/
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology InnerProductSpace
namespace GaussianComparison.GaussianModel

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

omit [IsProbabilityMeasure μ] in
theorem meanScaledDensity_mul_ratio (s : ℝ) (x : Space d) :
    meanScaledDensity ν s x * scaledRatio μ ν s x = meanScaledDensity μ s x := by
  rw [← density_ratio_eq_scaledRatio μ ν]
  field_simp [(meanScaledDensity_pos hM ν s x).ne']

omit hM [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem posterior_gap_inner (s : ℝ) (x : Space d) :
    ⟪meanScaledPosterior μ s x, meanScaledGap μ ν s x⟫_ℝ -
      ⟪meanScaledPosterior ν s x, meanScaledGap μ ν s x⟫_ℝ =
        ‖meanScaledGap μ ν s x‖ ^ 2 := by
  rw [← inner_sub_left]
  exact real_inner_self_eq_norm_sq _

theorem meanScalingKL_derivative_integral (s : ℝ) :
    (∫ x, phi x * scaledKLIntegrandDot μ ν s x) =
      s * ∫ x, meanScaledDensity μ s x * ‖meanScaledGap μ ν s x‖ ^ 2 := by
  let L := scaledLogRatio μ ν s
  let R := scaledRatio μ ν s
  let G := fun x => s • meanScaledGap μ ν s x
  let H := fun x => (R x * s) • meanScaledGap μ ν s x
  have hLc : Continuous L := by
    exact Continuous.comp (g := Function.uncurry (scaledLogRatio μ ν))
      (f := fun x : Space d => (s, x)) (continuous_scaledLogRatio hM μ ν)
      (continuous_const.prodMk continuous_id)
  have hRc : Continuous R := by
    exact Continuous.comp (g := Function.uncurry (scaledRatio μ ν))
      (f := fun x : Space d => (s, x)) (continuous_scaledRatio hM μ ν)
      (continuous_const.prodMk continuous_id)
  have hGc : Continuous G :=
    (continuous_const : Continuous (fun _ : Space d => s)).smul (continuous_meanScaledGap_space hM μ ν s)
  have hHc : Continuous H := (hRc.mul (continuous_const : Continuous (fun _ : Space d => s))).smul
    (continuous_meanScaledGap_space hM μ ν s)
  have hLb := fixed_growth s (fun T hT => scaledLogRatio_growth hM hT μ ν)
  have hRb := fixed_growth s (fun T hT => scaledRatio_growth hM hT μ ν)
  have hGb : ExpGrowth (fun (_ : Unit) x => G x) :=
    fixed_growth (f := fun r x => r • meanScaledGap μ ν r x) s
      (fun T hT => scaledLogRatio_gradient_growth hM μ ν hT)
  have hHb : ExpGrowth (fun (_ : Unit) x => H x) :=
    fixed_growth (f := fun r x => (scaledRatio μ ν r x * r) • meanScaledGap μ ν r x) s
      (fun T hT => scaledRatio_gradient_growth hM μ ν hT)
  have hdL (x : Space d) : HasGradientAt (fun y => L y + 1) (G x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (scaledLogRatio_hasGradientAt hM μ ν s x).hasFDerivAt.add_const 1
  have hμ := meanScaling_weak_derivative hM μ s (fun x => L x + 1) G
    (hLc.add continuous_const) hGc hdL (hLb.add (ExpGrowth.const 1)) hGb
  have hν := meanScaling_weak_derivative hM ν s R H hRc hHc
    (scaledRatio_hasGradientAt hM μ ν s) hRb hHb
  have iμ := integrable_scaledPartitionDot_mul hM μ s (hLc.add continuous_const)
    (hLb.add (ExpGrowth.const 1))
  have iν := integrable_scaledPartitionDot_mul hM ν s hRc hRb
  change Integrable (fun x => phi x * scaledPartitionDot μ s x * (L x + 1)) at iμ
  have jμ := integrable_meanScaledDensity_mul_inner hM μ s hGc hGb
  have jν := integrable_meanScaledDensity_mul_inner hM ν s hHc hHb
  calc
    _ = (∫ x, phi x * scaledPartitionDot μ s x * (L x + 1)) -
        ∫ x, phi x * scaledPartitionDot ν s x * R x := by
      rw [← integral_sub iμ iν]
      apply integral_congr_ae; filter_upwards [] with x
      dsimp [scaledKLIntegrandDot, L, R]; ring
    _ = (∫ x, meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ) -
        ∫ x, meanScaledDensity ν s x * ⟪meanScaledPosterior ν s x, H x⟫_ℝ := by rw [hμ, hν]
    _ = ∫ x, (meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ -
        meanScaledDensity ν s x * ⟪meanScaledPosterior ν s x, H x⟫_ℝ) := (integral_sub jμ jν).symm
    _ = s * ∫ x, meanScaledDensity μ s x * ‖meanScaledGap μ ν s x‖ ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae; filter_upwards [] with x
      dsimp [G, H, R]
      rw [real_inner_smul_right, real_inner_smul_right]
      have hr := meanScaledDensity_mul_ratio hM μ ν s x
      have hg := posterior_gap_inner μ ν s x
      rw [← hg, ← hr]
      ring

theorem meanScalingKL_hasDerivAt (s : ℝ) :
    HasDerivAt (fun r => kl volume (meanScaledDensity μ r) (meanScaledDensity ν r))
      (s * ∫ x, meanScaledDensity μ s x * ‖meanScaledGap μ ν s x‖ ^ 2) s := by
  rw [← meanScalingKL_derivative_integral hM μ ν s]
  exact meanScalingKL_hasDerivAt_integral hM μ ν s

theorem meanScalingJeffreys_hasDerivAt (s : ℝ) (hs : s ∈ Ioo 0 1) :
    HasDerivAt (meanScalingJeffreys μ ν) (meanScalingKLRate μ ν s) s := by
  have ha : |s| ≤ 1 := by rw [abs_of_nonneg hs.1.le]; exact hs.2.le
  have hiμ := integrable_mul_meanScaledGap_sq hM μ ν s (integrable_meanScaledDensity μ s ha)
    (continuous_meanScaledDensity_space μ s)
  have hiν := integrable_mul_meanScaledGap_sq hM μ ν s (integrable_meanScaledDensity ν s ha)
    (continuous_meanScaledDensity_space ν s)
  convert! (meanScalingKL_hasDerivAt hM μ ν s).add (meanScalingKL_hasDerivAt hM ν μ s) using 1
  unfold meanScalingKLRate
  simp only [meanScaledGap, norm_sub_rev] at *
  rw [← mul_add, ← integral_add hiμ hiν]
  congr 1; apply integral_congr_ae; filter_upwards [] with x; ring

theorem meanScaledDensity_mul_rootRatio (s : ℝ) (x : Space d) :
    meanScaledDensity μ s x * scaledRootRatio ν μ s x =
      sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) := by
  rw [scaledRootRatio, ← density_ratio_eq_scaledRatio ν μ]
  have hp := meanScaledDensity_pos hM μ s x
  have hq := meanScaledDensity_pos hM ν s x
  rw [sqrt_div hq.le, sqrt_mul hp.le]
  have hsp : sqrt (meanScaledDensity μ s x) ≠ 0 := (sqrt_pos.mpr hp).ne'
  field_simp
  nlinarith [sq_sqrt hp.le]

theorem meanScalingAffinity_derivative_integral (s : ℝ) :
    (∫ x, phi x * scaledAffinityIntegrandDot μ ν s x) =
      -s / 4 * ∫ x, sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) *
        ‖meanScaledGap μ ν s x‖ ^ 2 := by
  let R := scaledRootRatio ν μ s
  let S := scaledRootRatio μ ν s
  let G := fun x => (s / 2 * R x) • meanScaledGap ν μ s x
  let H := fun x => (s / 2 * S x) • meanScaledGap μ ν s x
  have hRc : Continuous R := by
    exact Continuous.comp (g := Function.uncurry (scaledRootRatio ν μ))
      (f := fun x : Space d => (s, x)) (continuous_scaledRootRatio hM ν μ)
      (continuous_const.prodMk continuous_id)
  have hSc : Continuous S := by
    exact Continuous.comp (g := Function.uncurry (scaledRootRatio μ ν))
      (f := fun x : Space d => (s, x)) (continuous_scaledRootRatio hM μ ν)
      (continuous_const.prodMk continuous_id)
  have hGc : Continuous G := ((continuous_const : Continuous (fun _ : Space d => s / 2)).mul hRc).smul
    (continuous_meanScaledGap_space hM ν μ s)
  have hHc : Continuous H := ((continuous_const : Continuous (fun _ : Space d => s / 2)).mul hSc).smul
    (continuous_meanScaledGap_space hM μ ν s)
  have hRb := fixed_growth s (fun T hT => scaledRootRatio_growth hM hT ν μ)
  have hSb := fixed_growth s (fun T hT => scaledRootRatio_growth hM hT μ ν)
  have hGb : ExpGrowth (fun (_ : Unit) x => G x) :=
    fixed_growth (f := fun r x => (r / 2 * scaledRootRatio ν μ r x) • meanScaledGap ν μ r x) s
      (fun T hT => scaledRootRatio_gradient_growth hM ν μ hT)
  have hHb : ExpGrowth (fun (_ : Unit) x => H x) :=
    fixed_growth (f := fun r x => (r / 2 * scaledRootRatio μ ν r x) • meanScaledGap μ ν r x) s
      (fun T hT => scaledRootRatio_gradient_growth hM μ ν hT)
  have hμ := meanScaling_weak_derivative hM μ s R G hRc hGc
    (scaledRootRatio_hasGradientAt hM ν μ s) hRb hGb
  have hν := meanScaling_weak_derivative hM ν s S H hSc hHc
    (scaledRootRatio_hasGradientAt hM μ ν s) hSb hHb
  have iμ := integrable_scaledPartitionDot_mul hM μ s hRc hRb
  have iν := integrable_scaledPartitionDot_mul hM ν s hSc hSb
  have jμ := integrable_meanScaledDensity_mul_inner hM μ s hGc hGb
  have jν := integrable_meanScaledDensity_mul_inner hM ν s hHc hHb
  calc
    _ = (1 / 2 : ℝ) * ((∫ x, phi x * scaledPartitionDot μ s x * R x) +
        ∫ x, phi x * scaledPartitionDot ν s x * S x) := by
      rw [← integral_add iμ iν, ← integral_const_mul]
      apply integral_congr_ae; filter_upwards [] with x
      dsimp [scaledAffinityIntegrandDot, R, S]; ring
    _ = (1 / 2 : ℝ) * ((∫ x, meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ) +
        ∫ x, meanScaledDensity ν s x * ⟪meanScaledPosterior ν s x, H x⟫_ℝ) := by rw [hμ, hν]
    _ = ∫ x, (1 / 2 : ℝ) * (meanScaledDensity μ s x * ⟪meanScaledPosterior μ s x, G x⟫_ℝ +
        meanScaledDensity ν s x * ⟪meanScaledPosterior ν s x, H x⟫_ℝ) := by
      rw [integral_const_mul, integral_add jμ jν]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae; filter_upwards [] with x
      dsimp [G, H, R, S]
      rw [real_inner_smul_right, real_inner_smul_right]
      have hr := meanScaledDensity_mul_rootRatio hM μ ν s x
      have hs := meanScaledDensity_mul_rootRatio hM ν μ s x
      rw [mul_comm (meanScaledDensity ν s x) (meanScaledDensity μ s x)] at hs
      have hg := posterior_gap_inner μ ν s x
      have hrev : meanScaledGap ν μ s x = -meanScaledGap μ ν s x := by
        simp [meanScaledGap, neg_sub]
      rw [hrev, inner_neg_right, ← hg]
      calc
        _ = s / 4 * ((meanScaledDensity ν s x * scaledRootRatio μ ν s x) *
            ⟪meanScaledPosterior ν s x, meanScaledGap μ ν s x⟫_ℝ -
          (meanScaledDensity μ s x * scaledRootRatio ν μ s x) *
            ⟪meanScaledPosterior μ s x, meanScaledGap μ ν s x⟫_ℝ) := by ring
        _ = _ := by rw [hr, hs]; ring

theorem meanScalingAffinity_hasDerivAt (s : ℝ) :
    HasDerivAt (fun r => affinity volume (meanScaledDensity μ r) (meanScaledDensity ν r))
      (-s / 4 * ∫ x, sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) *
        ‖meanScaledGap μ ν s x‖ ^ 2) s := by
  rw [← meanScalingAffinity_derivative_integral hM μ ν s]
  exact meanScalingAffinity_hasDerivAt_integral hM μ ν s

theorem meanScalingHellinger_hasDerivAt (s : ℝ) (hs : s ∈ Ioo 0 1) :
    HasDerivAt (meanScalingHellinger μ ν) (meanScalingHellingerRate μ ν s) s := by
  have he : meanScalingHellinger μ ν =ᶠ[𝓝 s]
      (fun r => 2 - 2 * affinity volume (meanScaledDensity μ r) (meanScaledDensity ν r)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    have ha : |r| ≤ 1 := by rw [abs_of_nonneg hr.1.le]; exact hr.2.le
    have h := (finiteDivergences_meanScaled hM μ ν r ha).hellingerSq_eq
    dsimp [meanScalingHellinger]
    linarith
  have hd := (hasDerivAt_const s (2 : ℝ)).sub ((meanScalingAffinity_hasDerivAt hM μ ν s).const_mul 2)
  convert! hd.congr_of_eventuallyEq he using 1
  unfold meanScalingHellingerRate
  ring

end GaussianComparison.GaussianModel
