import GaussianComparison.Divergences
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Elementary KL comparison: the deterministic final step

This module formalizes the algebra and one-variable calculus in the mean-scaling
proof. It does not assert the Gaussian divergence derivative identities.
`kl_comparison_of_derivative_bound` is an explicitly conditional analytic lemma;
its Gaussian instantiation requires separately proved derivative identities.
There are no stochastic imports or uses of the existing stochastic comparison.
-/

noncomputable section

open Real Set

namespace GaussianComparison.ElementaryKL

/-- Split a weighted symmetric density sum into its Hellinger part and affinity
part. This is the pointwise algebra used after the divergence derivatives. -/
theorem density_weight_split_bound {p q w M : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hw : w ≤ 4 * M ^ 2) :
    (p + q) * w ≤
      4 * M ^ 2 * (sqrt p - sqrt q) ^ 2 + 2 * sqrt (p * q) * w := by
  have hs := GaussianComparison.hellinger_integrand_eq hp hq
  have hm := mul_le_mul_of_nonneg_right hw (sq_nonneg (sqrt p - sqrt q))
  calc
    (p + q) * w = (sqrt p - sqrt q) ^ 2 * w + 2 * sqrt (p * q) * w := by
      rw [hs]
      ring
    _ ≤ 4 * M ^ 2 * (sqrt p - sqrt q) ^ 2 + 2 * sqrt (p * q) * w := by
      nlinarith

/-- The last step of the elementary proof, stated for actual differentiable
curves. Continuity at both endpoints and derivatives in the open interval are
explicit. The proof uses monotonicity instead of assuming an FTC identity. -/
theorem kl_comparison_of_derivative_bound (M : ℝ) (J D J' D' : ℝ → ℝ)
    (hJ : ContinuousOn J (Icc 0 1)) (hD : ContinuousOn D (Icc 0 1))
    (hJder : ∀ s ∈ Ioo 0 1, HasDerivAt J (J' s) s)
    (hDder : ∀ s ∈ Ioo 0 1, HasDerivAt D (D' s) s)
    (hDnonneg : ∀ s ∈ Ioo 0 1, 0 ≤ D' s)
    (hbound : ∀ s ∈ Ioo 0 1, J' s ≤ 4 * M ^ 2 * s * D s + 4 * D' s)
    (hJzero : J 0 = 0) (hDzero : D 0 = 0) :
    J 1 ≤ (2 * M ^ 2 + 4) * D 1 := by
  have hmono : MonotoneOn D (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hD
    · intro s hs
      rw [interior_Icc] at hs
      exact (hDder s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hDder s hs).deriv]
      exact hDnonneg s hs
  let F : ℝ → ℝ := fun s => J s - 4 * D s - 2 * M ^ 2 * s ^ 2 * D 1
  have hFcont : ContinuousOn F (Icc 0 1) := by
    exact (hJ.sub (hD.const_mul 4)).sub
      ((((continuousOn_id.pow 2).const_mul (2 * M ^ 2)).mul_const (D 1)))
  have hFder (s : ℝ) (hs : s ∈ Ioo 0 1) :
      HasDerivAt F (J' s - 4 * D' s - 4 * M ^ 2 * s * D 1) s := by
    convert! ((hJder s hs).sub ((hDder s hs).const_mul 4)).sub
      ((((hasDerivAt_id s).pow 2).const_mul (2 * M ^ 2)).mul_const (D 1)) using 1
    dsimp [F]
    ring
  have hanti : AntitoneOn F (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hFcont
    · intro s hs
      rw [interior_Icc] at hs
      exact (hFder s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hFder s hs).deriv]
      have hDle : D s ≤ D 1 :=
        hmono ⟨hs.1.le, hs.2.le⟩ ⟨by norm_num, le_rfl⟩ hs.2.le
      have hs0 : 0 ≤ s := hs.1.le
      have hm := mul_le_mul_of_nonneg_left hDle
        (show 0 ≤ 4 * M ^ 2 * s from by positivity)
      linarith [hbound s hs]
  have hend := hanti (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [F] at hend
  rw [hJzero, hDzero] at hend
  nlinarith

end GaussianComparison.ElementaryKL
