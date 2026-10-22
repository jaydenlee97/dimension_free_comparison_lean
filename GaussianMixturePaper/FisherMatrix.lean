import GaussianMixturePaper.DeBruijn
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Section 3: actual generator divergences and the Fisher information matrix

The scalar trace is identified with the trace of the entrywise-integrated
matrix. Integrability of every matrix entry is proved; it is not a hypothesis
on the three Gaussian-mixture specializations.
-/
noncomputable section
open MeasureTheory Real Filter
open scoped BigOperators InnerProductSpace
namespace GaussianComparison.GaussianModel

/-- Actual density f-divergence. Finiteness is supplied by the theorems below. -/
def densityFDivergence {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (p q : Ω → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x, q x * f (p x / q x) ∂m

theorem klGenerator_integrand {p q : ℝ} (hq : q ≠ 0) :
    q * klGenerator (p / q) = p * log (p / q) - p + q := by
  unfold klGenerator
  field_simp

theorem hellingerGenerator_integrand {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    q * hellingerGenerator (p / q) = (sqrt p - sqrt q) ^ 2 := by
  unfold hellingerGenerator
  rw [sqrt_div hp]
  have hs := sq_sqrt hq.le
  field_simp [(sqrt_pos.mpr hq).ne']
  nlinarith [sq_nonneg (sqrt p - sqrt q)]

theorem integrable_densityFDivergence_kl {Ω : Type*} [MeasurableSpace Ω]
    {m : Measure Ω} {p q : Ω → ℝ} (hf : FiniteDivergences m p q) :
    Integrable (fun x => q x * klGenerator (p x / q x)) m := by
  apply ((hf.integrable_kl.sub hf.integrable_p).add hf.integrable_q).congr
  filter_upwards [hf.positive_q] with x hx
  exact (klGenerator_integrand hx.ne').symm

theorem densityFDivergence_kl {Ω : Type*} [MeasurableSpace Ω]
    {m : Measure Ω} {p q : Ω → ℝ} (hf : FiniteDivergences m p q) :
    densityFDivergence m p q klGenerator = kl m p q := by
  unfold densityFDivergence
  have he : (fun x => q x * klGenerator (p x / q x)) =ᵐ[m]
      (fun x => p x * log (p x / q x) - p x + q x) := by
    filter_upwards [hf.positive_q] with x hx
    exact klGenerator_integrand hx.ne'
  rw [integral_congr_ae he]
  have hadd := integral_add (hf.integrable_kl.sub hf.integrable_p) hf.integrable_q
  simp only [Pi.sub_apply] at hadd
  rw [hadd, integral_sub hf.integrable_kl hf.integrable_p, hf.mass_p, hf.mass_q]
  unfold kl
  ring

theorem integrable_densityFDivergence_hellinger {Ω : Type*} [MeasurableSpace Ω]
    {m : Measure Ω} {p q : Ω → ℝ} (hf : FiniteDivergences m p q) :
    Integrable (fun x => q x * hellingerGenerator (p x / q x)) m := by
  apply hf.integrable_hellingerSq.congr
  filter_upwards [hf.positive_p, hf.positive_q] with x hp hq
  exact (hellingerGenerator_integrand hp.le hq).symm

theorem densityFDivergence_hellinger {Ω : Type*} [MeasurableSpace Ω]
    {m : Measure Ω} {p q : Ω → ℝ} (hf : FiniteDivergences m p q) :
    densityFDivergence m p q hellingerGenerator = hellingerSq m p q := by
  apply integral_congr_ae
  filter_upwards [hf.positive_p, hf.positive_q] with x hp hq
  exact hellingerGenerator_integrand hp.le hq

theorem integrable_densityFDivergence_chiSq {Ω : Type*} [MeasurableSpace Ω]
    {m : Measure Ω} {p q : Ω → ℝ} (hf : FiniteDivergences m p q) :
    Integrable (fun x => q x * chiSqGenerator (p x / q x)) m := by
  simpa only [chiSqGenerator, mul_comm] using hf.integrable_chiSq

theorem densityFDivergence_chiSq {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (p q : Ω → ℝ) :
    densityFDivergence m p q chiSqGenerator = chiSq m p q := by
  unfold densityFDivergence chiSq chiSqGenerator
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The entrywise integral of w(x) score(x) score(x)^T. -/
def scoreFisherMatrix {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M))
    (s : ℝ) (w : Space d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ x, w x * likelihoodScore μ ν s x i * likelihoodScore μ ν s x j

/-- The Fisher matrix in (3.1), including the actual generator curvature. -/
def generatorFisherMatrix {d : ℕ} {M : ℝ} (μ ν : Measure (Ball d M))
    (s : ℝ) (f : ℝ → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  scoreFisherMatrix μ ν s (fun x => meanScaledDensity ν s x *
    (meanScaledDensity μ s x / meanScaledDensity ν s x) ^ 2 *
    deriv (deriv f) (meanScaledDensity μ s x / meanScaledDensity ν s x))

variable {d : ℕ} {M : ℝ} (hM : 0 ≤ M)
  (μ ν : Measure (Ball d M)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
include hM

theorem continuous_likelihoodScore (s : ℝ) : Continuous (likelihoodScore μ ν s) := by
  have he : likelihoodScore μ ν s = fun x => s • meanScaledGap μ ν s x :=
    funext (likelihoodScore_eq hM μ ν s)
  rw [he]
  exact (continuous_const : Continuous (fun _ : Space d => s)).smul
    (continuous_meanScaledGap_space hM μ ν s)

theorem integrable_scoreFisherMatrix_entry {s : ℝ} {w : Space d → ℝ}
    (hw : Integrable w) (hwc : Continuous w) (i j : Fin d) :
    Integrable (fun x => w x * likelihoodScore μ ν s x i * likelihoodScore μ ν s x j) := by
  have hi := (integrable_scoreFisherTrace hM μ ν (s := s) hw hwc).norm
  apply hi.mono'
  · exact ((hwc.mul ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp (continuous_likelihoodScore hM μ ν s))).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).comp (continuous_likelihoodScore hM μ ν s))).aestronglyMeasurable
  · filter_upwards [] with x
    simp only [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    have hi := PiLp.norm_apply_le (likelihoodScore μ ν s x) i
    have hj := PiLp.norm_apply_le (likelihoodScore μ ν s x) j
    have hprod := mul_le_mul hi hj (norm_nonneg _) (norm_nonneg _)
    calc
      ‖w x‖ * ‖likelihoodScore μ ν s x i‖ * ‖likelihoodScore μ ν s x j‖ =
          ‖w x‖ * (‖likelihoodScore μ ν s x i‖ * ‖likelihoodScore μ ν s x j‖) := by ring
      _ ≤ ‖w x‖ * (‖likelihoodScore μ ν s x‖ * ‖likelihoodScore μ ν s x‖) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = _ := by ring

theorem scoreFisherMatrix_trace {s : ℝ} {w : Space d → ℝ}
    (hw : Integrable w) (hwc : Continuous w) :
    Matrix.trace (scoreFisherMatrix μ ν s w) = scoreFisherTrace μ ν s w := by
  change (∑ i : Fin d, ∫ x, w x * likelihoodScore μ ν s x i * likelihoodScore μ ν s x i) =
    ∫ x, w x * ‖likelihoodScore μ ν s x‖ ^ 2
  rw [← integral_finsetSum Finset.univ
    (fun i _ => integrable_scoreFisherMatrix_entry hM μ ν (s := s) hw hwc i i)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, sq_abs]
  ring

/-- The three density weights are integrable and continuous at every time. -/
theorem fisher_generator_weights (s : ℝ) :
    (Integrable (meanScaledDensity μ s) ∧ Continuous (meanScaledDensity μ s)) ∧
    (Integrable (fun x => sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) / 2) ∧
      Continuous (fun x => sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) / 2)) ∧
    (Integrable (fun x => 2 * (meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x)) ∧
      Continuous (fun x => 2 * (meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x))) := by
  have hf := finiteDivergences_meanScaled_global hM μ ν s
  exact ⟨⟨hf.integrable_p, continuous_meanScaledDensity_space μ s⟩,
    ⟨hf.integrable_affinity.div_const 2,
      (((continuous_meanScaledDensity_space μ s).mul (continuous_meanScaledDensity_space ν s)).sqrt).div_const 2⟩,
    ⟨hf.integrable_ratio_square.const_mul 2,
      continuous_const.mul (((continuous_meanScaledDensity_space μ s).pow 2).div
        (continuous_meanScaledDensity_space ν s) (fun x => (meanScaledDensity_pos hM ν s x).ne'))⟩⟩

/-- Exact membership in the three concrete generator family. -/
def IsPaperGenerator (f : ℝ → ℝ) : Prop :=
  f = klGenerator ∨ f = hellingerGenerator ∨ f = chiSqGenerator

/-- The scalar weight appearing in the matrix and scalar trace definitions. -/
def generatorDensityWeight (s : ℝ) (f : ℝ → ℝ) (x : Space d) : ℝ :=
  meanScaledDensity ν s x * (meanScaledDensity μ s x / meanScaledDensity ν s x) ^ 2 *
    deriv (deriv f) (meanScaledDensity μ s x / meanScaledDensity ν s x)

theorem generatorDensityWeight_regular (s : ℝ) (f : ℝ → ℝ) (hf : IsPaperGenerator f) :
    Integrable (generatorDensityWeight μ ν s f) ∧ Continuous (generatorDensityWeight μ ν s f) := by
  obtain rfl | rfl | rfl := hf
  · have he : generatorDensityWeight μ ν s klGenerator = meanScaledDensity μ s := by
      funext x
      exact klGenerator_weight (meanScaledDensity_pos hM μ s x) (meanScaledDensity_pos hM ν s x)
    rw [he]
    exact (fisher_generator_weights hM μ ν s).1
  · have he : generatorDensityWeight μ ν s hellingerGenerator =
        (fun x => sqrt (meanScaledDensity μ s x * meanScaledDensity ν s x) / 2) := by
      funext x
      exact hellingerGenerator_weight (meanScaledDensity_pos hM μ s x) (meanScaledDensity_pos hM ν s x)
    rw [he]
    exact (fisher_generator_weights hM μ ν s).2.1
  · have he : generatorDensityWeight μ ν s chiSqGenerator =
        (fun x => 2 * (meanScaledDensity μ s x ^ 2 / meanScaledDensity ν s x)) := by
      funext x
      exact chiSqGenerator_weight (meanScaledDensity_pos hM ν s x)
    rw [he]
    exact (fisher_generator_weights hM μ ν s).2.2

/-- Every entry of (3.1) is absolutely integrable for each paper generator. -/
theorem integrable_generatorFisherMatrix_entry (s : ℝ) (f : ℝ → ℝ)
    (hf : IsPaperGenerator f) (i j : Fin d) :
    Integrable (fun x => generatorDensityWeight μ ν s f x *
      likelihoodScore μ ν s x i * likelihoodScore μ ν s x j) := by
  obtain ⟨hi, hc⟩ := generatorDensityWeight_regular hM μ ν s f hf
  exact integrable_scoreFisherMatrix_entry hM μ ν (s := s) hi hc i j

/-- The actual matrix trace equals the scalar trace after (3.1). -/
theorem generatorFisherMatrix_trace (s : ℝ) (f : ℝ → ℝ) (hf : IsPaperGenerator f) :
    Matrix.trace (generatorFisherMatrix μ ν s f) = generatorFisherTrace μ ν s f := by
  obtain ⟨hi, hc⟩ := generatorDensityWeight_regular hM μ ν s f hf
  exact scoreFisherMatrix_trace hM μ ν (s := s) hi hc

/-- Finiteness of all three f-divergences along the full real interpolation. -/
theorem integrable_densityFDivergence_paper (s : ℝ) (f : ℝ → ℝ) (hf : IsPaperGenerator f) :
    Integrable (fun x => meanScaledDensity ν s x *
      f (meanScaledDensity μ s x / meanScaledDensity ν s x)) := by
  have hfinite := finiteDivergences_meanScaled_global hM μ ν s
  obtain rfl | rfl | rfl := hf
  · exact integrable_densityFDivergence_kl hfinite
  · exact integrable_densityFDivergence_hellinger hfinite
  · exact integrable_densityFDivergence_chiSq hfinite

/-- Equation (3.3) with the actual f-divergence and actual matrix trace,
for every paper generator and every real time, including zero. -/
theorem deBruijn_matrix (s : ℝ) (f : ℝ → ℝ) (hf : IsPaperGenerator f) :
    s * deriv (fun r => densityFDivergence volume (meanScaledDensity μ r)
      (meanScaledDensity ν r) f) s = Matrix.trace (generatorFisherMatrix μ ν s f) := by
  rw [generatorFisherMatrix_trace hM μ ν s f hf]
  obtain rfl | rfl | rfl := hf
  · have he : (fun r => densityFDivergence volume (meanScaledDensity μ r)
        (meanScaledDensity ν r) klGenerator) =
        (fun r => kl volume (meanScaledDensity μ r) (meanScaledDensity ν r)) := by
      funext r
      exact densityFDivergence_kl (finiteDivergences_meanScaled_global hM μ ν r)
    rw [he, generatorFisherTrace_kl hM μ ν s]
    exact deBruijn_kl hM μ ν s
  · have he : (fun r => densityFDivergence volume (meanScaledDensity μ r)
        (meanScaledDensity ν r) hellingerGenerator) = meanScalingHellinger μ ν := by
      funext r
      exact densityFDivergence_hellinger (finiteDivergences_meanScaled_global hM μ ν r)
    rw [he, generatorFisherTrace_hellinger hM μ ν s]
    exact deBruijn_hellinger hM μ ν s
  · have he : (fun r => densityFDivergence volume (meanScaledDensity μ r)
        (meanScaledDensity ν r) chiSqGenerator) = meanScalingChiSq μ ν := by
      funext r
      exact densityFDivergence_chiSq volume _ _
    rw [he, generatorFisherTrace_chiSq hM μ ν s]
    exact deBruijn_chiSq hM μ ν s

end GaussianComparison.GaussianModel
