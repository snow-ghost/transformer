import VerifiedClassifier.Frequency
import VerifiedClassifier.Numerical

namespace VerifiedClassifier.Frequency

open Filter
open scoped Topology
noncomputable section
variable {C L : Type*} [DecidableEq C] [DecidableEq L] [Fintype L] [Nonempty L]

/-- If empirical counts, scaled by a vanishing positive inverse sample size,
converge to the source probabilities, positive fixed smoothing preserves consistency.
This is a conditional theorem; it does not assume all training data have this property. -/
theorem smoothed_consistent (data : Nat → Data C L) (c : C) (α : Smoothing) (source : PMF L)
    (scale : Nat → ℝ) (scale_pos : ∀ n, 0 < scale n)
    (scale_zero : Tendsto scale atTop (𝓝 0))
    (empirical : ∀ a, Tendsto (fun n => (count (data n) c a : ℝ) * scale n)
      atTop (𝓝 (source a).toReal)) (a : L) :
    Tendsto (fun n => (predict (data n) α c a).toReal) atTop (𝓝 (source a).toReal) := by
  have hw : ∀ b, Tendsto (fun n => (weights (data n) α c).weight b * scale n)
      atTop (𝓝 (source b).toReal) := by
    intro b
    have h := (empirical b).add (scale_zero.const_mul α.val)
    simpa only [weights, add_mul, mul_zero, add_zero] using h
  have hs := tendsto_finsetSum Finset.univ (fun b _ => hw b)
  rw [Quality.source_sum] at hs
  have h := (hw a).div hs one_ne_zero
  simp only [div_one] at h
  apply h.congr
  intro n
  simp only [Pi.div_apply, predict, FiniteWeights.toPMF_toReal, FiniteWeights.probability]
  rw [← Finset.sum_mul, mul_div_mul_right _ _ (ne_of_gt (scale_pos n))]

theorem smoothed_risk_consistent (data : Nat → Data C L) (c : C) (α : Smoothing) (source : PMF L)
    (scale : Nat → ℝ) (scale_pos : ∀ n, 0 < scale n)
    (scale_zero : Tendsto scale atTop (𝓝 0))
    (empirical : ∀ a, Tendsto (fun n => (count (data n) c a : ℝ) * scale n)
      atTop (𝓝 (source a).toReal)) :
    Tendsto (fun n => Quality.risk source (fun a => (predict (data n) α c a).toReal)) atTop
      (𝓝 (Quality.risk source (fun a => (source a).toReal))) :=
  Numerical.risk_converges source _ (smoothed_consistent data c α source scale scale_pos scale_zero empirical)

end
end VerifiedClassifier.Frequency
