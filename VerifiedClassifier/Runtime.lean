import Std

namespace VerifiedClassifier.Runtime

/-- A finite exact categorical distribution represented by equally likely tickets. -/
structure TicketTable (L : Type) where
  tickets : List L
  nonempty : tickets ≠ []

def TicketTable.pick {L : Type} (table : TicketTable L) (ticket : Fin table.tickets.length) : L :=
  table.tickets.get ticket

def TicketTable.probability {L : Type} [BEq L] (table : TicketTable L) (label : L) : Rat :=
  (table.tickets.count label : Rat) / (table.tickets.length : Rat)

theorem TicketTable.pick_mem {L : Type} (table : TicketTable L) (ticket : Fin table.tickets.length) :
    table.pick ticket ∈ table.tickets := List.get_mem _ _

/-- IO supplies the random index. Correctness of its law is an external assumption. -/
def TicketTable.sample {L : Type} (table : TicketTable L) : IO L := do
  let n ← IO.rand 0 (table.tickets.length - 1)
  return table.pick ⟨n % table.tickets.length, Nat.mod_lt _ (List.length_pos_iff.mpr table.nonempty)⟩

def matching {C : Type} [DecidableEq C] (data : List (C × Bool)) (context : C) : List Bool :=
  data.filterMap (fun pair => if pair.1 = context then some pair.2 else none)

/-- Laplace smoothing with one prior ticket for each binary label. -/
def learnBool {C : Type} [DecidableEq C] (data : List (C × Bool)) (context : C) : TicketTable Bool :=
  ⟨[false, true] ++ matching data context, by simp⟩

/-- Rational binomial approximation to exp, with strictly positive iteration count. -/
def expApprox (iterations : Nat) (x : Rat) : Rat :=
  (1 + x / (iterations + 1 : Nat)) ^ (iterations + 1)

/-- For nonnegative scaled logits every approximate weight is positive.
All calculations here use exact rationals, with no floating-point rounding. -/
def softmaxApprox {k : Nat} (iterations : Nat) (scaledScores : Fin k → Rat) (a : Fin k) : Rat :=
  expApprox iterations (scaledScores a) /
    (List.ofFn (fun b => expApprox iterations (scaledScores b))).sum

end VerifiedClassifier.Runtime
