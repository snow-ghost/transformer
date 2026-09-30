import VerifiedClassifier.Runtime
import VerifiedClassifier.Quality
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace VerifiedClassifier.Numerical

open Filter
open scoped Topology
noncomputable section

theorem expApprox_cast (n : Nat) (x : Rat) :
    (Runtime.expApprox n x : ℝ) = (1 + (x : ℝ) / (n+1 : Nat)) ^ (n+1) := by
  simp [Runtime.expApprox]

/-- Executable rational approximations converge to the exact real exponential. -/
theorem expApprox_converges (x : Rat) :
    Tendsto (fun n => (Runtime.expApprox n x : ℝ)) atTop (𝓝 (Real.exp x)) := by
  simpa only [expApprox_cast, Function.comp_def] using
    (Real.tendsto_one_add_div_pow_exp (x : ℝ)).comp (tendsto_add_atTop_nat 1)

theorem expApprox_positive (n : Nat) (x : Rat) (hx : 0 ≤ x) :
    0 < (Runtime.expApprox n x : ℝ) := by
  rw [expApprox_cast]
  have h : 0 ≤ (x : ℝ) := by exact_mod_cast hx
  positivity

variable {k : Nat} [NeZero k]

omit [NeZero k] in
theorem softmaxApprox_cast (n : Nat) (scores : Fin k → Rat) (a : Fin k) :
    (Runtime.softmaxApprox n scores a : ℝ) =
      (Runtime.expApprox n (scores a) : ℝ) / ∑ b, (Runtime.expApprox n (scores b) : ℝ) := by
  simp [Runtime.softmaxApprox, List.sum_ofFn]

def approximateWeights (n : Nat) (scores : Fin k → Rat) (nonneg : ∀ a, 0 ≤ scores a) : FiniteWeights (Fin k) where
  weight a := Runtime.expApprox n (scores a)
  nonneg a := (expApprox_positive n _ (nonneg a)).le
  total_pos := Finset.sum_pos (fun a _ => expApprox_positive n _ (nonneg a)) Finset.univ_nonempty

/-- At each finite approximation order the executable table remains a valid distribution. -/
theorem softmaxApprox_normalized (n : Nat) (scores : Fin k → Rat) (nonneg : ∀ a, 0 ≤ scores a) :
    (∑ a, (Runtime.softmaxApprox n scores a : ℝ)) = 1 := by
  simp only [softmaxApprox_cast]
  exact (approximateWeights n scores nonneg).probability_sum

theorem softmaxApprox_nonneg (n : Nat) (scores : Fin k → Rat) (nonneg : ∀ a, 0 ≤ scores a) (a : Fin k) :
    0 ≤ (Runtime.softmaxApprox n scores a : ℝ) := by
  rw [softmaxApprox_cast]
  exact (approximateWeights n scores nonneg).probability_nonneg a

/-- Full convergence to the existing softmax semantics. Scores here are already divided by T. -/
theorem softmaxApprox_converges (scores : Fin k → Rat) (a : Fin k) :
    Tendsto (fun n => (Runtime.softmaxApprox n scores a : ℝ)) atTop
      (𝓝 ((Softmax.distribution (fun b => (scores b : ℝ)) Temperature.unit a).toReal)) := by
  have hs := tendsto_finsetSum Finset.univ (fun b _ => expApprox_converges (scores b))
  have hd : 0 < ∑ b, Real.exp (scores b : ℝ) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have h := (expApprox_converges (scores a)).div hs (ne_of_gt hd)
  rw [Softmax.unit_temperature, ENNReal.toReal_ofReal (div_pos (Real.exp_pos _) hd).le]
  exact h.congr (fun n => (softmaxApprox_cast n scores a).symm)

/-- Pointwise-consistent forecasts also converge in expected Brier risk on a finite alphabet. -/
theorem risk_converges {L : Type*} [Fintype L] [DecidableEq L]
    (source : PMF L) (forecasts : Nat → L → ℝ)
    (consistent : ∀ a, Tendsto (fun n => forecasts n a) atTop (𝓝 (source a).toReal)) :
    Tendsto (fun n => Quality.risk source (forecasts n)) atTop
      (𝓝 (Quality.risk source (fun a => (source a).toReal))) := by
  apply tendsto_finsetSum
  intro actual _
  apply tendsto_const_nhds.mul
  apply tendsto_finsetSum
  intro a _
  exact ((consistent a).sub tendsto_const_nhds).pow 2

end
end VerifiedClassifier.Numerical
