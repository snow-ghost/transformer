import VerifiedClassifier.Selection
import VerifiedClassifier.Sampling
import VerifiedClassifier.Rules

namespace VerifiedClassifier.Selection

variable {H C R : Type}

theorem best_le (score : H → Rat) (first : H) (rest : List H)
    (h : H) (member : h ∈ first :: rest) :
    score (best score first rest) ≤ score h := by
  induction rest generalizing first with
  | nil =>
    have eq : h = first := by simpa using member
    subst h
    exact le_rfl
  | cons next rest ih =>
    simp only [best]
    split_ifs with choice
    · rcases List.mem_cons.mp member with rfl | member
      · exact le_rfl
      · exact choice.trans (ih next member)
    · rcases List.mem_cons.mp member with rfl | member
      · exact (le_of_not_ge choice)
      · exact ih next member

theorem select_mem (validation : Validation C) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (penalty : Rat) (first : H) (rest : List H) :
    select validation models cost penalty first rest ∈ first :: rest :=
  best_mem _ _ _

theorem select_optimal (validation : Validation C) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (penalty : Rat) (first : H) (rest : List H)
    (h : H) (member : h ∈ first :: rest) :
    objective validation models cost penalty
      (select validation models cost penalty first rest) ≤
      objective validation models cost penalty h :=
  best_le _ _ _ h member

/-- Raising the structural penalty cannot increase the selected structural cost. -/
theorem cost_antitone (validation : Validation C) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (low high : Rat) (increases : low < high) (first : H) (rest : List H) :
    cost (select validation models cost high first rest) ≤
      cost (select validation models cost low first rest) := by
  have hl := select_optimal validation models cost low first rest _
    (select_mem validation models cost high first rest)
  have hh := select_optimal validation models cost high first rest _
    (select_mem validation models cost low first rest)
  simp only [objective] at hl hh
  by_contra contrary
  have hc : (cost (select validation models cost low first rest) : Rat) <
      cost (select validation models cost high first rest) := by
    exact_mod_cast Nat.lt_of_not_ge contrary
  nlinarith

noncomputable section
open scoped BigOperators

theorem loss_cast (forecast : Bool → Rat) (actual : Bool) :
    (loss forecast actual : ℝ) = Quality.brier (fun a => (forecast a : ℝ)) actual := by
  cases actual <;> simp [loss, Quality.brier, add_comm]

theorem empirical_cast (validation : Validation C) (model : C → Runtime.TicketTable Bool) :
    (empirical validation model : ℝ) =
      (validation.data.map (fun pair =>
        Quality.brier (fun a => (model pair.1).law a |>.toReal) pair.2)).sum /
      (validation.data.length : ℝ) := by
  simp only [empirical, Rat.cast_div, Rat.cast_natCast, Rat.cast_list_sum, List.map_map]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  simp only [Function.comp_apply, loss_cast, Runtime.TicketTable.rational_probability]

theorem fit_law [DecidableEq R] (key : C → R) (training : List (C × Bool)) (c : C) :
    (fit key training c).law = Rules.learned key training Frequency.laplace c :=
  Runtime.learnBool_law _ _

/-- Source contexts have an explicit finite probability law. -/
def population [Fintype C] (contexts : PMF C) (source : C → PMF Bool)
    (model : C → Runtime.TicketTable Bool) : ℝ :=
  ∑ c, (contexts c).toReal * Quality.risk (source c) (fun a => (model c).law a |>.toReal)

def bayesRisk [Fintype C] (contexts : PMF C) (source : C → PMF Bool) : ℝ :=
  ∑ c, (contexts c).toReal * Quality.risk (source c) (fun a => (source c a).toReal)

def approximation [Fintype C] (contexts : PMF C) (source : C → PMF Bool)
    (model : C → Runtime.TicketTable Bool) : ℝ :=
  ∑ c, (contexts c).toReal * Quality.squaredDistance
    (fun a => (source c a).toReal) (fun a => (model c).law a |>.toReal)

theorem population_decomposition [Fintype C] (contexts : PMF C) (source : C → PMF Bool)
    (model : C → Runtime.TicketTable Bool) :
    population contexts source model = bayesRisk contexts source + approximation contexts source model := by
  unfold population bayesRisk approximation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [Quality.risk_decomposition (source c) (fun a => ((model c).law a).toReal), mul_add]

/-- This is an explicit condition on validation accuracy, not an automatic property of data. -/
def Accurate (validation : Validation C) (models : H → C → Runtime.TicketTable Bool)
    (trueRisk : H → ℝ) (candidates : List H) (ε : ℝ) : Prop :=
  ∀ h ∈ candidates, |(empirical validation (models h) : ℝ) - trueRisk h| ≤ ε

/-- Selection competes with every listed candidate, allowing validation error and structural cost. -/
theorem oracle_bound (validation : Validation C) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (penalty : Rat) (first : H) (rest : List H)
    (trueRisk : H → ℝ) (ε : ℝ)
    (accurate : Accurate validation models trueRisk (first :: rest) ε)
    (h : H) (member : h ∈ first :: rest) :
    trueRisk (select validation models cost penalty first rest) +
      (penalty : ℝ) * cost (select validation models cost penalty first rest) ≤
    trueRisk h + (penalty : ℝ) * cost h + 2 * ε := by
  have optimum := select_optimal validation models cost penalty first rest h member
  have optimum' : (objective validation models cost penalty
      (select validation models cost penalty first rest) : ℝ) ≤
      (objective validation models cost penalty h : ℝ) := by exact_mod_cast optimum
  simp only [objective, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at optimum'
  have hs := (abs_le.mp (accurate _ (select_mem validation models cost penalty first rest))).1
  have hh := (abs_le.mp (accurate h member)).2
  linarith

/-- A gap exceeding twice the validation error identifies the unique preferred candidate. -/
theorem selects_of_gap (validation : Validation C) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (penalty : Rat) (first : H) (rest : List H)
    (trueRisk : H → ℝ) (ε : ℝ)
    (accurate : Accurate validation models trueRisk (first :: rest) ε)
    (h : H) (member : h ∈ first :: rest)
    (gap : ∀ g ∈ first :: rest, g ≠ h →
      trueRisk h + (penalty : ℝ) * cost h + 2 * ε < trueRisk g + (penalty : ℝ) * cost g) :
    select validation models cost penalty first rest = h := by
  by_contra different
  have lower := gap _ (select_mem validation models cost penalty first rest) different
  have upper := oracle_bound validation models cost penalty first rest trueRisk ε accurate h member
  exact (not_lt_of_ge upper) lower

theorem excess_risk_bound [Fintype C] (validation : Validation C)
    (models : H → C → Runtime.TicketTable Bool) (cost : H → Nat)
    (penalty : Rat) (penalty_nonneg : 0 ≤ penalty) (first : H) (rest : List H)
    (contexts : PMF C) (source : C → PMF Bool) (ε : ℝ)
    (accurate : Accurate validation models (fun h => population contexts source (models h))
      (first :: rest) ε) (h : H) (member : h ∈ first :: rest) :
    population contexts source (models (select validation models cost penalty first rest)) -
      bayesRisk contexts source ≤
      approximation contexts source (models h) + (penalty : ℝ) * cost h + 2 * ε := by
  have bound := oracle_bound validation models cost penalty first rest _ ε accurate h member
  rw [population_decomposition contexts source (models h)] at bound
  have hp : 0 ≤ (penalty : ℝ) := by exact_mod_cast penalty_nonneg
  have hc : 0 ≤ (penalty : ℝ) * cost (select validation models cost penalty first rest) :=
    mul_nonneg hp (Nat.cast_nonneg _)
  linarith

end
end VerifiedClassifier.Selection
