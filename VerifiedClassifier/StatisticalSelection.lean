import VerifiedClassifier.Concentration

namespace VerifiedClassifier.Selection

open MeasureTheory ProbabilityTheory
noncomputable section

/-- Radius for K fixed candidates, n fresh IID validation observations, and failure level δ. -/
def confidenceRadius (n K : Nat) (δ : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (2 * K / δ) / n)

theorem confidenceRadius_pos {n K : Nat} [NeZero n] [NeZero K]
    (δ : ℝ) (positive : 0 < δ) (atMostOne : δ ≤ 1) :
    0 < confidenceRadius n K δ := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  have ratio : 1 < 2 * (K : ℝ) / δ := (lt_div_iff₀ positive).mpr (by nlinarith)
  exact Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) (Real.log_pos ratio)) hn)

theorem failure_at_radius {n K : Nat} [NeZero n] [NeZero K]
    (δ : ℝ) (positive : 0 < δ) (atMostOne : δ ≤ 1) :
    2 * K * Real.exp (-(n : ℝ) * (confidenceRadius n K δ)^2 / 2) = δ := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have rad : 0 ≤ 2 * Real.log (2 * K / δ) / n :=
    (Real.sqrt_pos.mp (confidenceRadius_pos (n := n) (K := K) δ positive atMostOne)).le
  rw [confidenceRadius, Real.sq_sqrt rad]
  have algebra : -(n : ℝ) * (2 * Real.log (2 * K / δ) / n) / 2 = -Real.log (2 * K / δ) := by
    field_simp
  rw [algebra, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

/-- A sufficient validation sample size for any requested positive accuracy. -/
theorem confidenceRadius_le_of_sample_size {n K : Nat} [NeZero n]
    (δ ε : ℝ) (accuracy_positive : 0 < ε)
    (enough : 2 * Real.log (2 * K / δ) / ε^2 ≤ n) :
    confidenceRadius n K δ ≤ ε := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hs := (div_le_iff₀ (sq_pos_of_pos accuracy_positive)).mp enough
  apply (Real.sqrt_le_left accuracy_positive.le).mpr
  exact (div_le_iff₀ hn).mpr (by nlinarith)

variable {C : Type} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- The previous `Accurate` premise now holds with a proved probability bound. -/
theorem accuracy_probability_ge {H : Type} {n : Nat} [NeZero n]
    (contexts : PMF C) (source : C → PMF Bool) (models : H → C → Runtime.TicketTable Bool)
    (first : H) (rest : List H) (δ : ℝ) (positive : 0 < δ) (atMostOne : δ ≤ 1) :
    1 - δ ≤ (validationLaw n contexts source).real
      {sample | Accurate (sampledValidation sample) models
        (fun h => population contexts source (models h)) (first :: rest)
        (confidenceRadius n (rest.length + 1) δ)} := by
  let ε := confidenceRadius n (rest.length + 1) δ
  have hε : 0 ≤ ε := (confidenceRadius_pos (n := n) (K := rest.length + 1) δ positive atMostOne).le
  have fail := uniform_deviation_probability_le (n := n) contexts source models (first :: rest) ε hε
  simp only [List.length_cons] at fail
  rw [failure_at_radius δ positive atMostOne] at fail
  let good : Set (Fin n → C × Bool) := {sample | Accurate (sampledValidation sample) models
    (fun h => population contexts source (models h)) (first :: rest) ε}
  have total := measureReal_add_measureReal_compl (μ := validationLaw n contexts source)
    (Set.to_countable good).measurableSet
  simp only [probReal_univ] at total
  change (validationLaw n contexts source).real goodᶜ ≤ δ at fail
  change 1 - δ ≤ (validationLaw n contexts source).real good
  linarith

theorem accuracy_probability_of_sample_size {H : Type} {n : Nat} [NeZero n]
    (contexts : PMF C) (source : C → PMF Bool) (models : H → C → Runtime.TicketTable Bool)
    (first : H) (rest : List H) (δ ε : ℝ)
    (positive : 0 < δ) (atMostOne : δ ≤ 1) (accuracy_positive : 0 < ε)
    (enough : 2 * Real.log (2 * (rest.length + 1) / δ) / ε^2 ≤ n) :
    1 - δ ≤ (validationLaw n contexts source).real
      {sample | Accurate (sampledValidation sample) models
        (fun h => population contexts source (models h)) (first :: rest) ε} := by
  have radius := confidenceRadius_le_of_sample_size (n := n) (K := rest.length + 1)
    δ ε accuracy_positive (by simpa only [Nat.cast_add, Nat.cast_one] using enough)
  apply (accuracy_probability_ge (n := n) contexts source models first rest δ positive atMostOne).trans
  refine measureReal_mono ?_ (by finiteness)
  intro sample accurate h member
  exact (accurate h member).trans radius

/-- One good validation event simultaneously controls comparison with every candidate. -/
theorem selection_probability_ge {H : Type} {n : Nat} [NeZero n]
    (contexts : PMF C) (source : C → PMF Bool) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (penalty : Rat) (first : H) (rest : List H)
    (δ : ℝ) (positive : 0 < δ) (atMostOne : δ ≤ 1) :
    1 - δ ≤ (validationLaw n contexts source).real
      {sample | ∀ h ∈ first :: rest,
        let selected := select (sampledValidation sample) models cost penalty first rest
        population contexts source (models selected) + (penalty : ℝ) * cost selected ≤
          population contexts source (models h) + (penalty : ℝ) * cost h +
            2 * confidenceRadius n (rest.length + 1) δ} := by
  apply (accuracy_probability_ge (n := n) contexts source models first rest δ positive atMostOne).trans
  refine measureReal_mono ?_ (by finiteness)
  intro sample accurate h member
  exact oracle_bound (sampledValidation sample) models cost penalty first rest _ _ accurate h member

theorem excess_risk_probability_ge {H : Type} {n : Nat} [NeZero n]
    (contexts : PMF C) (source : C → PMF Bool) (models : H → C → Runtime.TicketTable Bool)
    (cost : H → Nat) (penalty : Rat) (penalty_nonneg : 0 ≤ penalty) (first : H) (rest : List H)
    (δ : ℝ) (positive : 0 < δ) (atMostOne : δ ≤ 1) :
    1 - δ ≤ (validationLaw n contexts source).real
      {sample | ∀ h ∈ first :: rest,
        population contexts source
            (models (select (sampledValidation sample) models cost penalty first rest)) -
          bayesRisk contexts source ≤
        approximation contexts source (models h) + (penalty : ℝ) * cost h +
          2 * confidenceRadius n (rest.length + 1) δ} := by
  apply (accuracy_probability_ge (n := n) contexts source models first rest δ positive atMostOne).trans
  refine measureReal_mono ?_ (by finiteness)
  intro sample accurate h member
  exact excess_risk_bound (sampledValidation sample) models cost penalty penalty_nonneg first rest
    contexts source _ accurate h member

end
end VerifiedClassifier.Selection
