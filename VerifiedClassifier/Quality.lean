import VerifiedClassifier.Temperature
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace VerifiedClassifier
namespace Quality

noncomputable section
open scoped BigOperators
variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Squared error of the full probability vector against the observed label. -/
def brier (forecast : L → ℝ) (actual : L) : ℝ :=
  ∑ a, (forecast a - if a = actual then 1 else 0) ^ 2

def risk (source : PMF L) (forecast : L → ℝ) : ℝ :=
  ∑ actual, (source actual).toReal * brier forecast actual

def squaredDistance (p q : L → ℝ) : ℝ := ∑ a, (q a - p a) ^ 2

omit [DecidableEq L] in
theorem source_sum (source : PMF L) : ∑ a, (source a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => source.apply_ne_top a)]
  have h : ∑ a, source a = 1 := by simpa only [tsum_fintype] using source.tsum_coe
  rw [h]
  rfl

theorem brier_nonneg (forecast : L → ℝ) (actual : L) : 0 ≤ brier forecast actual :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem risk_nonneg (source : PMF L) (forecast : L → ℝ) : 0 ≤ risk source forecast :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (brier_nonneg _ _))

theorem brier_expansion (forecast : L → ℝ) (actual : L) :
    brier forecast actual = (∑ a, forecast a ^ 2) - 2 * forecast actual + 1 := by
  unfold brier
  have term : ∀ a, (forecast a - if a = actual then 1 else 0) ^ 2 =
      forecast a ^ 2 + if a = actual then 1 - 2 * forecast a else 0 := by
    intro a
    split_ifs <;> ring
  simp_rw [term, Finset.sum_add_distrib]
  simp
  ring

theorem risk_expansion (source : PMF L) (forecast : L → ℝ) :
    risk source forecast = (∑ a, forecast a ^ 2) -
      2 * (∑ a, (source a).toReal * forecast a) + 1 := by
  simp only [risk, brier_expansion, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_one, ← Finset.sum_mul, source_sum, one_mul]
  have term : ∀ a, (source a).toReal * (2 * forecast a) = 2 * ((source a).toReal * forecast a) := by
    intro a
    ring
  simp_rw [term, ← Finset.mul_sum]

/-- Exact excess risk: reporting the true distribution uniquely minimizes expected Brier loss. -/
theorem risk_decomposition (source : PMF L) (forecast : L → ℝ) :
    risk source forecast = risk source (fun a => (source a).toReal) +
      squaredDistance (fun a => (source a).toReal) forecast := by
  rw [risk_expansion, risk_expansion]
  unfold squaredDistance
  have term : ∀ a, (forecast a - (source a).toReal)^2 =
      forecast a ^ 2 - 2 * ((source a).toReal * forecast a) + (source a).toReal ^ 2 := by
    intro a
    ring
  simp_rw [term, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← pow_two]
  ring

theorem truthful_minimizes (source : PMF L) (forecast : L → ℝ) :
    risk source (fun a => (source a).toReal) ≤ risk source forecast := by
  rw [risk_decomposition source forecast]
  have h : 0 ≤ squaredDistance (fun a => (source a).toReal) forecast :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem risk_eq_minimum_iff (source : PMF L) (forecast : L → ℝ) :
    risk source forecast = risk source (fun a => (source a).toReal) ↔
      ∀ a, forecast a = (source a).toReal := by
  rw [risk_decomposition, add_eq_left]
  unfold squaredDistance
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp [sub_eq_zero]

end
end Quality
end VerifiedClassifier
