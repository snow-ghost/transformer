import VerifiedClassifier.Choice
import VerifiedClassifier.SelectionGuarantees

namespace VerifiedClassifier.Choice
variable {k : Nat} [NeZero k]

theorem selected_maximal (table : Runtime.TicketTable (Fin k)) (a : Fin k) :
    (choose table).probabilities a ≤ (choose table).probabilities (choose table).selected := by
  have best := Selection.best_le (fun a => -table.probability a) 0 (List.finRange k) a (by simp)
  exact neg_le_neg_iff.mp best

noncomputable section

theorem probabilities_correct (table : Runtime.TicketTable (Fin k)) (a : Fin k) :
    ((choose table).probabilities a : ℝ) = (table.law a).toReal := table.rational_probability a

theorem probabilities_sum (table : Runtime.TicketTable (Fin k)) :
    (∑ a, ((choose table).probabilities a : ℝ)) = 1 := by
  simp_rw [probabilities_correct]
  exact Quality.source_sum _

theorem selected_mode (table : Runtime.TicketTable (Fin k)) : IsMode table.law (choose table).selected := by
  intro a
  apply (ENNReal.toReal_le_toReal (table.law.apply_ne_top a) (table.law.apply_ne_top _)).mp
  rw [← probabilities_correct, ← probabilities_correct]
  exact_mod_cast selected_maximal table a

omit [NeZero k] in
theorem matching_count {C : Type} [DecidableEq C] (data : List (C × Fin k)) (context : C) (a : Fin k) :
    (matching data context).count a = Frequency.count data context a := by
  induction data with
  | nil => simp [matching, Frequency.count]
  | cons pair rest ih =>
    rcases pair with ⟨c,b⟩
    by_cases same : c = context
    · subst c
      simpa [matching, Frequency.count, List.count_cons, beq_iff_eq] using ih
    · simpa [matching, Frequency.count, same] using ih

theorem learn_count {C : Type} [DecidableEq C] (data : List (C × Fin k)) (context : C) (a : Fin k) :
    (learn data context).tickets.count a = Frequency.count data context a+1 := by
  simp [learn,matching_count,Nat.add_comm]

theorem learn_law {C : Type} [DecidableEq C] (data : List (C × Fin k)) (context : C) :
    (learn data context).law = Frequency.predict data Frequency.laplace context := by
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' ((learn data context).law.apply_ne_top a)
    ((Frequency.predict data Frequency.laplace context).apply_ne_top a)).mp
  have total : (∑ b : Fin k, (learn data context).tickets.count b) = (learn data context).tickets.length := by
    have counts (xs : List (Fin k)) : (∑ b, xs.count b) = xs.length := by
      induction xs with
      | nil => simp
      | cons b rest ih => simp [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, ih]
    exact counts _
  simp_rw [learn_count] at total
  rw [Runtime.TicketTable.law_formula,Frequency.probability_formula]
  simp only [learn_count, ENNReal.toReal_div, ENNReal.toReal_natCast, Frequency.laplace, Nat.cast_add, Nat.cast_one, Fintype.card_fin, mul_one]
  congr 1
  have totalNat : (learn data context).tickets.length = (∑ b, Frequency.count data context b)+k := by
    simpa [Finset.sum_add_distrib] using total.symm
  exact_mod_cast totalNat

end
end VerifiedClassifier.Choice
