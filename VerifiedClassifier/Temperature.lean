import VerifiedClassifier.Classifier
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity

namespace VerifiedClassifier

open scoped BigOperators

noncomputable section

/-- Positive temperature only. Greedy selection is represented separately. -/
abbrev Temperature := { t : ℝ // 0 < t }

namespace Temperature

def unit : Temperature := ⟨1, zero_lt_one⟩

end Temperature

/-- Nonnegative weights with positive total mass on a finite label space. -/
structure FiniteWeights (L : Type*) [Fintype L] where
  weight : L → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total_pos : 0 < ∑ a, weight a

namespace FiniteWeights

variable {L : Type*} [Fintype L]

def probability (weights : FiniteWeights L) (a : L) : ℝ :=
  weights.weight a / ∑ b, weights.weight b

theorem probability_nonneg (weights : FiniteWeights L) (a : L) :
    0 ≤ weights.probability a := div_nonneg (weights.nonneg a) weights.total_pos.le

theorem probability_sum (weights : FiniteWeights L) :
    ∑ a, weights.probability a = 1 := by
  simp only [probability, ← Finset.sum_div]
  exact div_self (ne_of_gt weights.total_pos)

theorem probability_le_one (weights : FiniteWeights L) (a : L) :
    weights.probability a ≤ 1 := by
  rw [probability, div_le_one weights.total_pos]
  exact Finset.single_le_sum (fun b _ => weights.nonneg b) (Finset.mem_univ a)

theorem probability_le_iff (weights : FiniteWeights L) (a b : L) :
    weights.probability a ≤ weights.probability b ↔ weights.weight a ≤ weights.weight b :=
  div_le_div_iff_of_pos_right weights.total_pos

/-- Exact real probabilities embedded in Mathlib's discrete probability type. -/
def toPMF (weights : FiniteWeights L) : PMF L :=
  PMF.ofFintype (fun a => ENNReal.ofReal (weights.probability a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => weights.probability_nonneg a)]
    simp [weights.probability_sum])

@[simp] theorem toPMF_apply (weights : FiniteWeights L) (a : L) :
    weights.toPMF a = ENNReal.ofReal (weights.probability a) := rfl

theorem toPMF_le_iff (weights : FiniteWeights L) (a b : L) :
    weights.toPMF a ≤ weights.toPMF b ↔ weights.weight a ≤ weights.weight b := by
  rw [toPMF_apply, toPMF_apply,
    ENNReal.ofReal_le_ofReal_iff (weights.probability_nonneg b)]
  exact weights.probability_le_iff a b

@[simp] theorem toPMF_toReal (weights : FiniteWeights L) (a : L) :
    (weights.toPMF a).toReal = weights.probability a :=
  ENNReal.toReal_ofReal (weights.probability_nonneg a)

end FiniteWeights

namespace Softmax

variable {L : Type*} [Fintype L] [Nonempty L]

def weights (logits : L → ℝ) (temperature : Temperature) : FiniteWeights L where
  weight a := Real.exp (logits a / temperature.val)
  nonneg _ := (Real.exp_pos _).le
  total_pos := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

def distribution (logits : L → ℝ) (temperature : Temperature) : PMF L :=
  (weights logits temperature).toPMF

theorem probability_formula (logits : L → ℝ) (temperature : Temperature) (a : L) :
    distribution logits temperature a =
      ENNReal.ofReal (Real.exp (logits a / temperature.val) /
        ∑ b, Real.exp (logits b / temperature.val)) := rfl

theorem normalized (logits : L → ℝ) (temperature : Temperature) :
    ∑ a, distribution logits temperature a = 1 := by
  simpa only [tsum_fintype] using (distribution logits temperature).tsum_coe

/-- Positive temperature preserves all score comparisons, including ties. -/
theorem order_iff (logits : L → ℝ) (temperature : Temperature) (a b : L) :
    distribution logits temperature a ≤ distribution logits temperature b ↔
      logits a ≤ logits b := by
  rw [distribution, FiniteWeights.toPMF_le_iff]
  change Real.exp (logits a / temperature.val) ≤ Real.exp (logits b / temperature.val) ↔ _
  rw [Real.exp_le_exp, div_le_div_iff_of_pos_right temperature.property]

theorem mode_iff (logits : L → ℝ) (temperature : Temperature) (a : L) :
    IsMode (distribution logits temperature) a ↔ ∀ b, logits b ≤ logits a := by
  simp only [IsMode, order_iff]

theorem modes_temperature_independent (logits : L → ℝ) (t₁ t₂ : Temperature) (a : L) :
    IsMode (distribution logits t₁) a ↔ IsMode (distribution logits t₂) a := by
  rw [mode_iff, mode_iff]

/-- Temperature changes relative odds even though it preserves the modes. -/
theorem odds_formula (logits : L → ℝ) (temperature : Temperature) (a b : L) :
    (weights logits temperature).probability a / (weights logits temperature).probability b =
      Real.exp ((logits a - logits b) / temperature.val) := by
  unfold FiniteWeights.probability
  rw [div_div_div_cancel_right₀ (ne_of_gt (weights logits temperature).total_pos)]
  change Real.exp (logits a / temperature.val) / Real.exp (logits b / temperature.val) = _
  rw [← Real.exp_sub, ← sub_div]

/-- Lower temperature increases the odds of a higher-scoring label over a lower one. -/
theorem colder_odds (logits : L → ℝ) (cold warm : Temperature)
    (temperatures : cold.val ≤ warm.val) (a b : L) (scores : logits b ≤ logits a) :
    (weights logits warm).probability a / (weights logits warm).probability b ≤
      (weights logits cold).probability a / (weights logits cold).probability b := by
  rw [odds_formula, odds_formula, Real.exp_le_exp]
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr scores) cold.property temperatures

theorem positive (logits : L → ℝ) (temperature : Temperature) (a : L) :
    0 < distribution logits temperature a := by
  rw [probability_formula, ENNReal.ofReal_pos]
  exact div_pos (Real.exp_pos _) (weights logits temperature).total_pos

theorem support_full (logits : L → ℝ) (temperature : Temperature) :
    (distribution logits temperature).support = Set.univ := by
  ext a
  simp only [PMF.mem_support_iff, Set.mem_univ, iff_true]
  exact ne_of_gt (positive logits temperature a)

theorem unit_temperature (logits : L → ℝ) (a : L) :
    distribution logits Temperature.unit a =
      ENNReal.ofReal (Real.exp (logits a) / ∑ b, Real.exp (logits b)) := by
  simp [probability_formula, Temperature.unit]

/-- An arbitrary scoring algorithm becomes a probabilistic classifier. -/
def classifier {C M P : Type*} (scores : P → M → C → L → ℝ)
    (temperature : Temperature) : Classifier C L M P :=
  ⟨fun p m c => distribution (scores p m c) temperature⟩

end Softmax
end
end VerifiedClassifier
