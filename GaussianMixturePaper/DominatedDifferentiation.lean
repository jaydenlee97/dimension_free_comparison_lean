import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!+# Dominated differentiation: the analytic content of Lemma 4

`lemma4_dominated_differentiation` proves the integral derivative and the full
`C¹` conclusion on an open set, with an explicit derivative field `H'`.
`lemma4_from_ae_contDiff` derives its derivative and continuity assumptions from
almost-everywhere `C¹` slices and proves derivative-section measurability by
measurable difference quotients. Thus no derivative measurability is assumed in
the latter formulation. Measurable sections are weaker than the manuscript's
joint measurability assumption, and an arbitrary open set generalizes an interval.
The two integrable envelopes are the separate integrability consequences of the
manuscript's nonnegative `P_K + Q_K` envelope. No sigma-finiteness is needed here.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace GaussianMixturePaper

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {I : Set ℝ} {H H' : ℝ → X → ℝ}

/-- Measurability of a derivative section follows from measurable difference
quotients; it need not be assumed as an extra analytic condition. -/
theorem aestronglyMeasurable_derivative_section
    (hH : ∀ s : ℝ, AEStronglyMeasurable (H s) μ)
    {t : ℝ} {D : X → ℝ}
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun s => H s x) (D x) t) :
    AEStronglyMeasurable D μ := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : Tendsto r atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Filter.Eventually.of_forall fun n => by
        simp only [mem_compl_iff, mem_singleton_iff]
        dsimp [r]
        positivity
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => (r n)⁻¹ • (H (t + r n) x - H t x))
  · intro n
    exact ((hH (t + r n)).sub (hH t)).const_smul ((r n)⁻¹)
  · exact hd.mono fun x hx => hx.tendsto_slope_zero.comp hr

/-- Local version of derivative-section measurability. Extension by zero is used
only to make the difference quotients measurable outside the parameter domain. -/
theorem aestronglyMeasurable_derivative_section_on
    (hI : IsOpen I) (hH : ∀ s ∈ I, AEStronglyMeasurable (H s) μ)
    {t : ℝ} (ht : t ∈ I) {D : X → ℝ}
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun s => H s x) (D x) t) :
    AEStronglyMeasurable D μ := by
  classical
  let G : ℝ → X → ℝ := fun s x => if s ∈ I then H s x else 0
  have hG : ∀ s, AEStronglyMeasurable (G s) μ := by
    intro s
    by_cases hs : s ∈ I
    · simpa [G, hs] using hH s hs
    · simpa [G, hs] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : X => (0 : ℝ)) μ)
  apply aestronglyMeasurable_derivative_section (H := G) hG
  exact hd.mono fun x hx => hx.congr_of_eventuallyEq
    (Filter.eventually_of_mem (hI.mem_nhds ht) fun s hs => by simp [G, hs])

/-- Local dominated differentiation and continuity of the integrated derivative.
The envelopes control all parameters in a common compact interval outside one
null set, just as in (A.15)--(A.16). -/
theorem dominated_differentiation_local
    (hI : IsOpen I)
    (hH : ∀ t ∈ I, AEStronglyMeasurable (H t) μ)
    (hH' : ∀ t ∈ I, AEStronglyMeasurable (H' t) μ)
    (hderiv : ∀ᵐ x ∂μ, ∀ t ∈ I, HasDerivAt (fun s => H s x) (H' t x) t)
    (hcont : ∀ᵐ x ∂μ, ContinuousOn (fun t => H' t x) I)
    (hdom : ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ P Q : X → ℝ, Integrable P μ ∧ Integrable Q μ ∧
        (∀ᵐ x ∂μ, ∀ t ∈ Icc a b, ‖H t x‖ ≤ P x ∧ ‖H' t x‖ ≤ Q x))
    {t : ℝ} (ht : t ∈ I) :
    Integrable (H t) μ ∧ Integrable (H' t) μ ∧
      HasDerivAt (fun s => ∫ x, H s x ∂μ) (∫ x, H' t x ∂μ) t ∧
      ContinuousAt (fun s => ∫ x, H' s x ∂μ) t := by
  obtain ⟨a, b, htab, hab_nhds, habI⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hI.mem_nhds ht)
  obtain ⟨P, Q, hP, hQ, hbound⟩ := hdom a b habI
  have hHint : Integrable (H t) μ :=
    hP.mono' (hH t ht) (hbound.mono fun x hx => (hx t htab).1)
  have hHm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (H s) μ :=
    Filter.eventually_of_mem (hI.mem_nhds ht) fun s hs => hH s hs
  have hH'm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (H' s) μ :=
    Filter.eventually_of_mem (hI.mem_nhds ht) fun s hs => hH' s hs
  have hQbound : ∀ᵐ x ∂μ, ∀ s ∈ Icc a b, ‖H' s x‖ ≤ Q x :=
    hbound.mono fun x hx s hs => (hx s hs).2
  have hd : ∀ᵐ x ∂μ, ∀ s ∈ Icc a b,
      HasDerivAt (fun z => H z x) (H' s x) s :=
    hderiv.mono fun x hx s hs => hx s (habI hs)
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hab_nhds hHm hHint (hH' t ht) hQbound hQ hd
  refine ⟨hHint, hdiff.1, hdiff.2, ?_⟩
  refine continuousAt_of_dominated hH'm ?_ hQ ?_
  · exact Filter.eventually_of_mem hab_nhds fun s hs =>
      hQbound.mono fun x hx => hx s hs
  · exact hcont.mono fun x hx => (hx t ht).continuousAt (hI.mem_nhds ht)

/-- Lemma 4 with an explicit measurable derivative field. Both finiteness of
the integrals and continuous differentiability are conclusions, not assumptions. -/
theorem lemma4_dominated_differentiation
    (hI : IsOpen I)
    (hH : ∀ t ∈ I, AEStronglyMeasurable (H t) μ)
    (hH' : ∀ t ∈ I, AEStronglyMeasurable (H' t) μ)
    (hderiv : ∀ᵐ x ∂μ, ∀ t ∈ I, HasDerivAt (fun s => H s x) (H' t x) t)
    (hcont : ∀ᵐ x ∂μ, ContinuousOn (fun t => H' t x) I)
    (hdom : ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ P Q : X → ℝ, Integrable P μ ∧ Integrable Q μ ∧
        (∀ᵐ x ∂μ, ∀ t ∈ Icc a b, ‖H t x‖ ≤ P x ∧ ‖H' t x‖ ≤ Q x)) :
    ContDiffOn ℝ 1 (fun t => ∫ x, H t x ∂μ) I ∧
      ∀ t ∈ I, Integrable (H t) μ ∧ Integrable (H' t) μ ∧
        HasDerivAt (fun s => ∫ x, H s x ∂μ) (∫ x, H' t x ∂μ) t := by
  have hlocal := fun t ht => dominated_differentiation_local
    hI hH hH' hderiv hcont hdom (t := t) ht
  constructor
  · apply (contDiffOn_one_iff_derivWithin hI.uniqueDiffOn).2
    constructor
    · intro t ht
      exact (hlocal t ht).2.2.1.differentiableAt.differentiableWithinAt
    · have hc : ContinuousOn (fun t => ∫ x, H' t x ∂μ) I :=
        fun t ht => (hlocal t ht).2.2.2.continuousWithinAt
      apply hc.congr
      intro t ht
      exact (hlocal t ht).2.2.1.hasDerivWithinAt.derivWithin
        (hI.uniqueDiffOn t ht)
  · intro t ht
    exact ⟨(hlocal t ht).1, (hlocal t ht).2.1, (hlocal t ht).2.2.1⟩

/-- Paper-style Lemma 4: almost-everywhere `C¹` parameter slices and compact
interval envelopes imply `C¹` of the integral and the derivative formula (A.17).
Separate integrability of the two envelopes is equivalent to the manuscript's
integrability of their sum when, as in the manuscript, both are nonnegative.
Only measurable sections are needed, not joint measurability or sigma-finiteness. -/
theorem lemma4_from_ae_contDiff
    (hI : IsOpen I)
    (hH : ∀ t ∈ I, AEStronglyMeasurable (H t) μ)
    (hC1 : ∀ᵐ x ∂μ, ContDiffOn ℝ 1 (fun t => H t x) I)
    (hdom : ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ P Q : X → ℝ, Integrable P μ ∧ Integrable Q μ ∧
        (∀ᵐ x ∂μ, ∀ t ∈ Icc a b,
          ‖H t x‖ ≤ P x ∧ ‖deriv (fun s => H s x) t‖ ≤ Q x)) :
    ContDiffOn ℝ 1 (fun t => ∫ x, H t x ∂μ) I ∧
      ∀ t ∈ I, Integrable (H t) μ ∧
        Integrable (fun x => deriv (fun s => H s x) t) μ ∧
        HasDerivAt (fun s => ∫ x, H s x ∂μ)
          (∫ x, deriv (fun s => H s x) t ∂μ) t := by
  have hd : ∀ᵐ x ∂μ, ∀ t ∈ I,
      HasDerivAt (fun s => H s x) (deriv (fun s => H s x) t) t := by
    filter_upwards [hC1] with x hx
    intro t ht
    exact ((hx.differentiableOn (by norm_num) t ht).differentiableAt
      (hI.mem_nhds ht)).hasDerivAt
  have hm : ∀ t ∈ I,
      AEStronglyMeasurable (fun x => deriv (fun s => H s x) t) μ := by
    intro t ht
    apply aestronglyMeasurable_derivative_section_on hI hH ht
    exact hd.mono fun x hx => hx t ht
  have hc : ∀ᵐ x ∂μ, ContinuousOn (fun t => deriv (fun s => H s x) t) I :=
    hC1.mono fun x hx => hx.continuousOn_deriv_of_isOpen hI (by norm_num)
  exact lemma4_dominated_differentiation hI hH hm hd hc hdom

/-- Lemma 4 with the manuscript's nonnegative, sum-integrable envelopes.
The common exceptional null sets are expressed by the outer `∀ᵐ` quantifiers.
Joint measurability in the paper implies the section measurability used here. -/
theorem lemma4_nonnegative_envelopes
    (hI : IsOpen I)
    (hH : ∀ t ∈ I, AEStronglyMeasurable (H t) μ)
    (hC1 : ∀ᵐ x ∂μ, ContDiffOn ℝ 1 (fun t => H t x) I)
    (hdom : ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ P Q : X → ℝ,
        AEStronglyMeasurable P μ ∧ AEStronglyMeasurable Q μ ∧
        (∀ x, 0 ≤ P x) ∧ (∀ x, 0 ≤ Q x) ∧
        Integrable (fun x => P x + Q x) μ ∧
        (∀ᵐ x ∂μ, ∀ t ∈ Icc a b,
          ‖H t x‖ ≤ P x ∧ ‖deriv (fun s => H s x) t‖ ≤ Q x)) :
    ContDiffOn ℝ 1 (fun t => ∫ x, H t x ∂μ) I ∧
      ∀ t ∈ I, Integrable (H t) μ ∧
        Integrable (fun x => deriv (fun s => H s x) t) μ ∧
        HasDerivAt (fun s => ∫ x, H s x ∂μ)
          (∫ x, deriv (fun s => H s x) t ∂μ) t := by
  apply lemma4_from_ae_contDiff hI hH hC1
  intro a b hab
  obtain ⟨P, Q, hPm, hQm, hP0, hQ0, hPQ, hb⟩ := hdom a b hab
  refine ⟨P, Q, ?_, ?_, hb⟩
  · apply hPQ.mono' hPm
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x)]
      exact le_add_of_nonneg_right (hQ0 x)
  · apply hPQ.mono' hQm
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 x)]
      exact le_add_of_nonneg_left (hP0 x)

/-- The paper's joint measurability assumption is needed only on `I × X`.
Taking a measurable constant parameter yields every required section. -/
theorem measurable_sections_of_jointly_measurable_on
    (hjoint : Measurable (fun z : I × X => H z.1 z.2)) :
    ∀ t ∈ I, AEStronglyMeasurable (H t) μ := by
  intro t ht
  exact (hjoint.comp
    ((measurable_const : Measurable (fun _ : X => (⟨t, ht⟩ : I))).prodMk
      measurable_id)).aestronglyMeasurable

/-- Lemma 4 in the manuscript's joint-measurability formulation, with the
finite nonnegative integral of `P+Q` expressed by `Integrable (P+Q)`.
An open interval is a special case of the arbitrary open set used here. -/
theorem lemma4
    (hI : IsOpen I)
    (hjoint : Measurable (fun z : I × X => H z.1 z.2))
    (hC1 : ∀ᵐ x ∂μ, ContDiffOn ℝ 1 (fun t => H t x) I)
    (hdom : ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ P Q : X → ℝ,
        Measurable P ∧ Measurable Q ∧
        (∀ x, 0 ≤ P x) ∧ (∀ x, 0 ≤ Q x) ∧
        Integrable (fun x => P x + Q x) μ ∧
        (∀ᵐ x ∂μ, ∀ t ∈ Icc a b,
          ‖H t x‖ ≤ P x ∧ ‖deriv (fun s => H s x) t‖ ≤ Q x)) :
    ContDiffOn ℝ 1 (fun t => ∫ x, H t x ∂μ) I ∧
      ∀ t ∈ I, Integrable (H t) μ ∧
        Integrable (fun x => deriv (fun s => H s x) t) μ ∧
        HasDerivAt (fun s => ∫ x, H s x ∂μ)
          (∫ x, deriv (fun s => H s x) t ∂μ) t := by
  apply lemma4_nonnegative_envelopes hI
    (measurable_sections_of_jointly_measurable_on hjoint) hC1
  intro a b hab
  obtain ⟨P, Q, hPm, hQm, hP0, hQ0, hPQ, hb⟩ := hdom a b hab
  exact ⟨P, Q, hPm.aestronglyMeasurable, hQm.aestronglyMeasurable, hP0, hQ0, hPQ, hb⟩

end GaussianMixturePaper
