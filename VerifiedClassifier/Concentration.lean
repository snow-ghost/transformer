import VerifiedClassifier.ValidationSampling
import Mathlib.Probability.Moments.SubGaussian

namespace VerifiedClassifier.Selection

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

variable {C : Type} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

theorem centered_loss_subgaussian (n : Nat) (contexts : PMF C) (source : C → PMF Bool)
    (model : C → Runtime.TicketTable Bool) (i : Fin n) :
    HasSubgaussianMGF
      (fun sample => observationLoss model (sample i) - population contexts source model)
      1 (validationLaw n contexts source) := by
  have h := hasSubgaussianMGF_of_mem_Icc
    (μ := validationLaw n contexts source)
    (measurable_of_countable (fun sample : Fin n → C × Bool =>
      observationLoss model (sample i))).aemeasurable
    (ae_of_all _ (fun sample => observationLoss_bounds model (sample i)))
  rw [integral_coordinate_loss] at h
  norm_num at h
  exact h

theorem centered_sum_subgaussian (n : Nat) (contexts : PMF C) (source : C → PMF Bool)
    (model : C → Runtime.TicketTable Bool) :
    HasSubgaussianMGF
      (fun sample => ∑ i : Fin n,
        (observationLoss model (sample i) - population contexts source model))
      (n : NNReal) (validationLaw n contexts source) := by
  have independent : iIndepFun
      (fun i (sample : Fin n → C × Bool) =>
        observationLoss model (sample i) - population contexts source model)
      (validationLaw n contexts source) := by
    exact iIndepFun_pi
      (μ := fun _ : Fin n => (observationLaw contexts source).toMeasure)
      (X := fun _ : Fin n => fun pair : C × Bool =>
        observationLoss model pair - population contexts source model)
      (fun _ => (measurable_of_countable _).aemeasurable)
  have h := HasSubgaussianMGF.sum_of_iIndepFun independent (s := Finset.univ)
    (c := fun _ => 1) (fun i _ => centered_loss_subgaussian n contexts source model i)
  simpa using h

omit [MeasurableSpace C] [MeasurableSingletonClass C] in
theorem centered_sum_eq {n : Nat} [NeZero n] (contexts : PMF C) (source : C → PMF Bool)
    (model : C → Runtime.TicketTable Bool) (sample : Fin n → C × Bool) :
    (∑ i : Fin n, (observationLoss model (sample i) - population contexts source model)) =
      (n : ℝ) * ((empirical (sampledValidation sample) model : ℝ) -
        population contexts source model) := by
  rw [sampled_empirical, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

/-- Two-sided Hoeffding bound for the existing executable Brier average. -/
theorem deviation_probability_le {n : Nat} [NeZero n]
    (contexts : PMF C) (source : C → PMF Bool) (model : C → Runtime.TicketTable Bool)
    (ε : ℝ) (nonneg : 0 ≤ ε) :
    (validationLaw n contexts source).real
      {sample | ε < |(empirical (sampledValidation sample) model : ℝ) - population contexts source model|} ≤
      2 * Real.exp (-(n : ℝ) * ε^2 / 2) := by
  let total := fun sample : Fin n → C × Bool =>
    ∑ i : Fin n, (observationLoss model (sample i) - population contexts source model)
  have hsub := centered_sum_subgaussian n contexts source model
  have threshold : 0 ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) nonneg
  have upper := hsub.measure_ge_le threshold
  have lower := hsub.neg.measure_ge_le threshold
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have exponent : -((n : ℝ) * ε)^2 / (2 * (n : ℝ)) = -(n : ℝ) * ε^2 / 2 := by
    field_simp
  simp only [NNReal.coe_natCast, exponent] at upper lower
  have subset :
      {sample | ε < |(empirical (sampledValidation sample) model : ℝ) - population contexts source model|} ⊆
      {sample | (n : ℝ) * ε ≤ total sample} ∪ {sample | (n : ℝ) * ε ≤ -total sample} := by
    intro sample h
    change ε < |(empirical (sampledValidation sample) model : ℝ) - population contexts source model| at h
    have ht : total sample = (n : ℝ) *
        ((empirical (sampledValidation sample) model : ℝ) - population contexts source model) :=
      centered_sum_eq contexts source model sample
    rcases le_abs.mp h.le with h | h
    · left
      change (n : ℝ) * ε ≤ total sample
      rw [ht]
      exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    · right
      change (n : ℝ) * ε ≤ -total sample
      rw [ht]
      nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)]
  have hu := measureReal_union_le (μ := validationLaw n contexts source)
    {sample | (n : ℝ) * ε ≤ total sample} {sample | (n : ℝ) * ε ≤ -total sample}
  have hm := measureReal_mono (μ := validationLaw n contexts source) subset
  change (validationLaw n contexts source).real {sample | (n : ℝ) * ε ≤ total sample} ≤ _ at upper
  change (validationLaw n contexts source).real {sample | (n : ℝ) * ε ≤ -total sample} ≤ _ at lower
  linarith

/-- A finite union bound; independence between different candidates is unnecessary. -/
theorem uniform_deviation_probability_le {H : Type} {n : Nat} [NeZero n]
    (contexts : PMF C) (source : C → PMF Bool) (models : H → C → Runtime.TicketTable Bool)
    (candidates : List H) (ε : ℝ) (nonneg : 0 ≤ ε) :
    (validationLaw n contexts source).real
      {sample | ¬Accurate (sampledValidation sample) models
        (fun h => population contexts source (models h)) candidates ε} ≤
      2 * candidates.length * Real.exp (-(n : ℝ) * ε^2 / 2) := by
  induction candidates with
  | nil => simp [Accurate]
  | cons h rest ih =>
    have event :
        {sample : Fin n → C × Bool | ¬Accurate (sampledValidation sample) models
          (fun h => population contexts source (models h)) (h :: rest) ε} =
        {sample | ε < |(empirical (sampledValidation sample) (models h) : ℝ) -
          population contexts source (models h)|} ∪
        {sample | ¬Accurate (sampledValidation sample) models
          (fun h => population contexts source (models h)) rest ε} := by
      ext sample
      simp [Accurate, imp_iff_not_or]
    rw [event]
    have hu := measureReal_union_le (μ := validationLaw n contexts source)
      {sample | ε < |(empirical (sampledValidation sample) (models h) : ℝ) -
        population contexts source (models h)|}
      {sample | ¬Accurate (sampledValidation sample) models
        (fun h => population contexts source (models h)) rest ε}
    have single := deviation_probability_le (n := n) contexts source (models h) ε nonneg
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

end
end VerifiedClassifier.Selection
