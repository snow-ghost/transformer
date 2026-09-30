import VerifiedClassifier.Runtime
import VerifiedClassifier.Frequency

namespace VerifiedClassifier.Runtime

noncomputable section
open scoped ENNReal
variable {L : Type} [DecidableEq L]

def TicketTable.uniformIndex (table : TicketTable L) : PMF (Fin table.tickets.length) :=
  PMF.ofFintype (fun _ => (table.tickets.length : ENNReal)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast Nat.ne_of_gt (List.length_pos_iff.mpr table.nonempty)) (by simp))

def TicketTable.law (table : TicketTable L) : PMF L := table.uniformIndex.map table.pick

omit [DecidableEq L] in
theorem TicketTable.samples (table : TicketTable L) : Samples table.uniformIndex table.pick table.law := rfl

theorem count_as_sum (tickets : List L) (a : L) :
    (∑ i : Fin tickets.length, if tickets.get i = a then (1 : ENNReal) else 0) = tickets.count a := by
  induction tickets with
  | nil => simp
  | cons b rest ih =>
    simp only [List.length_cons, Fin.sum_univ_succ]
    change (if b = a then (1 : ENNReal) else 0) +
      (∑ i : Fin rest.length, if rest.get i = a then 1 else 0) = _
    rw [ih]
    simp only [List.count_cons, beq_iff_eq, Nat.cast_add]
    by_cases h : b = a <;> simp [h, add_comm]

/-- General exact categorical sampling: probability is multiplicity / ticket count. -/
theorem TicketTable.law_formula (table : TicketTable L) (a : L) :
    table.law a = (table.tickets.count a : ENNReal) / table.tickets.length := by
  classical
  rw [law, PMF.map_apply, tsum_fintype]
  rw [← count_as_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : table.tickets[i.val] = a
  · simp [pick, uniformIndex, h]
  · simp [pick, h, Ne.symm h]

/-- The executable rational report agrees with the mathematical sampling law. -/
theorem TicketTable.rational_probability (table : TicketTable L) (a : L) :
    (table.probability a : ℝ) = (table.law a).toReal := by
  rw [law_formula]
  simp [probability, ENNReal.toReal_div]

theorem matching_count {C : Type} [DecidableEq C] (data : List (C × Bool)) (c : C) (b : Bool) :
    (matching data c).count b = Frequency.count data c b := by
  induction data with
  | nil => simp [matching, Frequency.count]
  | cons pair rest ih =>
    rcases pair with ⟨d, a⟩
    by_cases h : d = c
    · subst d
      simp [matching, Frequency.count, List.count_cons, beq_iff_eq] at ih ⊢
      exact ih
    · simp [matching, Frequency.count, h] at ih ⊢
      exact ih

theorem learnBool_count {C : Type} [DecidableEq C] (data : List (C × Bool)) (c : C) (b : Bool) :
    (learnBool data c).tickets.count b = Frequency.count data c b + 1 := by
  cases b <;> simp [learnBool, matching_count, Nat.add_comm]

theorem bool_count_total (xs : List Bool) : xs.count true + xs.count false = xs.length := by
  induction xs with
  | nil => rfl
  | cons b rest ih => cases b <;> simp_all <;> omega

/-- The runnable learner and exact sampler implement the formal Laplace classifier. -/
theorem learnBool_law {C : Type} [DecidableEq C] (data : List (C × Bool)) (c : C) :
    (learnBool data c).law = Frequency.predict data Frequency.laplace c := by
  apply PMF.ext
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' ((learnBool data c).law.apply_ne_top b)
    ((Frequency.predict data Frequency.laplace c).apply_ne_top b)).mp
  have hlen := bool_count_total (learnBool data c).tickets
  rw [learnBool_count, learnBool_count] at hlen
  rw [TicketTable.law_formula, Frequency.probability_formula]
  simp [learnBool_count, ← hlen, Frequency.laplace, ENNReal.toReal_div, ENNReal.toReal_add]
  congr 1
  ring

end
end VerifiedClassifier.Runtime
