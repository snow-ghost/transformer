import VerifiedClassifier.Selection

namespace VerifiedClassifier.Choice

/-- Executable probabilities and a deterministic most-probable label. -/
structure Result (k : Nat) where
  probabilities : Fin k → Rat
  selected : Fin k

variable {k : Nat} [NeZero k]

/-- Ties retain the earliest maximum in 0 :: finRange k. -/
def choose (table : Runtime.TicketTable (Fin k)) : Result k :=
  ⟨table.probability,Selection.best (fun a => -table.probability a) 0 (List.finRange k)⟩

def matching {C : Type} [DecidableEq C] (data : List (C × Fin k)) (context : C) : List (Fin k) :=
  data.filterMap (fun pair => if pair.1 = context then some pair.2 else none)

/-- One prior ticket per class and one ticket per matching observation. -/
def learn {C : Type} [DecidableEq C] (data : List (C × Fin k)) (context : C) : Runtime.TicketTable (Fin k) :=
  ⟨List.finRange k ++ matching data context,by
    have h : (List.finRange k).length = k := by simp
    intro empty
    have length := congrArg List.length empty
    simp only [List.length_append, List.length_nil, h] at length
    have pos := Nat.pos_of_ne_zero (NeZero.ne k)
    omega⟩

end VerifiedClassifier.Choice
