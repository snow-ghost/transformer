import VerifiedClassifier.Quality
import Mathlib.Tactic.FieldSimp

namespace VerifiedClassifier
namespace Frequency

/-- Positive pseudocount; independent of decoding temperature. -/
structure Smoothing where
  val : ℝ
  property : 0 < val

def laplace : Smoothing := ⟨1, zero_lt_one⟩

variable {C L : Type*} [DecidableEq C] [DecidableEq L]

/-- A finite, unbounded-size log of supervised observations. -/
abbrev Data (C L : Type*) := List (C × L)

def count (data : Data C L) (context : C) (label : L) : Nat := data.count (context, label)

def observe (data : Data C L) (context : C) (label : L) : Data C L := (context, label) :: data

def train (data samples : Data C L) : Data C L := samples ++ data

theorem count_observe (data : Data C L) (c d : C) (a b : L) :
    count (observe data c a) d b = count data d b + if (c, a) = (d, b) then 1 else 0 := by
  simp only [count, observe, List.count_cons, beq_iff_eq]

theorem count_train (data samples : Data C L) (c : C) (a : L) :
    count (train data samples) c a = count samples c a + count data c a := by
  simp [count, train]

theorem count_permutation {xs ys : Data C L} (h : xs.Perm ys) (c : C) (a : L) :
    count xs c a = count ys c a := h.count_eq (c, a)

noncomputable section
variable [Fintype L] [Nonempty L]

def weights (data : Data C L) (α : Smoothing) (context : C) : FiniteWeights L where
  weight a := count data context a + α.val
  nonneg _ := (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) α.property).le
  total_pos := Finset.sum_pos (fun _ _ =>
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) α.property) Finset.univ_nonempty

def predict (data : Data C L) (α : Smoothing) (context : C) : PMF L :=
  (weights data α context).toPMF

/-- The program is the positive pseudocount; the memory is the observation log. -/
def classifier : Classifier C L (Data C L) Smoothing := ⟨fun α data c => predict data α c⟩

theorem positive (data : Data C L) (α : Smoothing) (c : C) (a : L) :
    0 < predict data α c a := by
  rw [predict, FiniteWeights.toPMF_apply, ENNReal.ofReal_pos]
  apply div_pos _ (weights data α c).total_pos
  change 0 < (count data c a : ℝ) + α.val
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) α.property

theorem probability_formula (data : Data C L) (α : Smoothing) (c : C) (a : L) :
    (predict data α c a).toReal =
      ((count data c a : ℝ) + α.val) /
      ((∑ b, (count data c b : ℝ)) + Fintype.card L * α.val) := by
  simp only [predict, FiniteWeights.toPMF_toReal, FiniteWeights.probability, weights,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem permutation_invariant {xs ys : Data C L} (h : xs.Perm ys) (α : Smoothing) (c : C) :
    predict xs α c = predict ys α c := by
  have hc : ∀ d a, count xs d a = count ys d a := count_permutation h
  simp only [predict, FiniteWeights.toPMF, FiniteWeights.probability, weights, hc]

theorem observe_other_context (data : Data C L) (α : Smoothing)
    (c d : C) (a : L) (h : c ≠ d) : predict (observe data c a) α d = predict data α d := by
  have hc : ∀ b, count (observe data c a) d b = count data d b := by
    intro b
    simp [count_observe, h]
  simp only [predict, FiniteWeights.toPMF, FiniteWeights.probability, weights, hc]

theorem total_weight_observe (data : Data C L) (α : Smoothing) (c : C) (a : L) :
    (∑ b, (weights (observe data c a) α c).weight b) =
      (∑ b, (weights data α c).weight b) + 1 := by
  have term : ∀ b, (weights (observe data c a) α c).weight b =
      (weights data α c).weight b + if b = a then 1 else 0 := by
    intro b
    simp only [weights, count_observe, Prod.mk.injEq, true_and, Nat.cast_add]
    by_cases hab : a = b <;> simp [hab, eq_comm]
    ring
  simp_rw [term, Finset.sum_add_distrib]
  simp

/-- An observation cannot reduce the predicted probability of its own label. -/
theorem observed_probability_increases (data : Data C L) (α : Smoothing) (c : C) (a : L) :
    (predict data α c a).toReal ≤ (predict (observe data c a) α c a).toReal := by
  simp only [predict, FiniteWeights.toPMF_toReal, FiniteWeights.probability]
  rw [total_weight_observe]
  have num : (weights (observe data c a) α c).weight a = (weights data α c).weight a + 1 := by
    simp [weights, count_observe]
    ring
  rw [num]
  have hd := (weights data α c).total_pos
  have hx : (weights data α c).weight a ≤ ∑ b, (weights data α c).weight b :=
    Finset.single_le_sum (fun b _ => (weights data α c).nonneg b) (Finset.mem_univ a)
  rw [div_le_div_iff₀ hd (by linarith)]
  nlinarith

end
end Frequency
end VerifiedClassifier
