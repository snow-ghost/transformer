import VerifiedClassifier.Runtime

namespace VerifiedClassifier.Selection

variable {H C R : Type}

/-- Exhaustive minimization over a nonempty candidate list, preserving the first tie. -/
def best (score : H → Rat) (first : H) : List H → H
  | [] => first
  | h :: rest =>
    let later := best score h rest
    if score first ≤ score later then first else later

theorem best_mem (score : H → Rat) (first : H) (rest : List H) :
    best score first rest ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp [best]
  | cons h rest ih =>
    simp only [best]
    split
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- Binary Brier score, in exact executable rational arithmetic. -/
def loss (forecast : Bool → Rat) (actual : Bool) : Rat :=
  (forecast false - if actual = false then 1 else 0)^2 +
  (forecast true - if actual = true then 1 else 0)^2

/-- Nonempty validation data make the average a genuine empirical loss. -/
structure Validation (C : Type) where
  data : List (C × Bool)
  nonempty : data ≠ []

def empirical (validation : Validation C) (model : C → Runtime.TicketTable Bool) : Rat :=
  (validation.data.map (fun pair => loss (model pair.1).probability pair.2)).sum /
    (validation.data.length : Rat)

/-- Fitting uses only the training data; validation is supplied separately to selection. -/
def fit [DecidableEq R] (key : C → R) (training : List (C × Bool))
    (c : C) : Runtime.TicketTable Bool :=
  Runtime.learnBool (training.map (fun pair => (key pair.1, pair.2))) (key c)

/-- A structural cost proxy: number of distinct keys on an explicitly supplied domain. -/
def cells [BEq R] (domain : List C) (key : C → R) : Nat :=
  (domain.map key).eraseDups.length

def objective (validation : Validation C) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (penalty : Rat) (h : H) : Rat :=
  empirical validation (models h) + penalty * (cost h : Rat)

def select (validation : Validation C) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (penalty : Rat) (first : H) (rest : List H) : H :=
  best (objective validation models cost penalty) first rest

/-- Instrumented search: count logical score calls, excluding their internal cost. -/
def bestMeasured (score : H → Rat) (first : H) : List H → H × Nat
  | [] => (first, 0)
  | h :: rest =>
    let later := bestMeasured score h rest
    (if score first ≤ score later.1 then first else later.1, later.2 + 2)

theorem bestMeasured_value (score : H → Rat) (first : H) (rest : List H) :
    (bestMeasured score first rest).1 = best score first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons h rest ih => simp only [bestMeasured, best, ih]

theorem bestMeasured_calls (score : H → Rat) (first : H) (rest : List H) :
    (bestMeasured score first rest).2 = 2 * rest.length := by
  induction rest generalizing first with
  | nil => rfl
  | cons h rest ih => simp [bestMeasured, ih, Nat.mul_add]

end VerifiedClassifier.Selection
