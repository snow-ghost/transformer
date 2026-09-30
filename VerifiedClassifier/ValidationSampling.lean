import VerifiedClassifier.SelectionGuarantees
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic

namespace VerifiedClassifier.Selection

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

variable {C : Type} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- Joint law of one context and its next binary symbol. -/
def observationLaw (contexts : PMF C) (source : C → PMF Bool) : PMF (C × Bool) :=
  PMF.ofFintype (fun pair => contexts pair.1 * source pair.1 pair.2) (by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    have hs (c : C) : ∑ b, source c b = 1 := by
      simpa only [tsum_fintype] using (source c).tsum_coe
    simp_rw [hs, mul_one]
    simpa only [tsum_fintype] using contexts.tsum_coe)

omit [MeasurableSpace C] [MeasurableSingletonClass C] in
theorem observationLaw_apply (contexts : PMF C) (source : C → PMF Bool) (c : C) (a : Bool) :
    observationLaw contexts source (c, a) = contexts c * source c a := rfl

/-- The validation observations are independent and identically distributed by construction. -/
def validationLaw (n : Nat) (contexts : PMF C) (source : C → PMF Bool) :
    Measure (Fin n → C × Bool) :=
  Measure.pi (fun _ => (observationLaw contexts source).toMeasure)

instance validationLaw_probability (n : Nat) (contexts : PMF C) (source : C → PMF Bool) :
    IsProbabilityMeasure (validationLaw n contexts source) := by
  unfold validationLaw
  infer_instance

/-- Reuse the existing executable validation interface on a random sample. -/
def sampledValidation {n : Nat} [NeZero n] (sample : Fin n → C × Bool) : Validation C :=
  ⟨List.ofFn sample, by
    intro h
    have length := congrArg List.length h
    exact (NeZero.ne n) (by simpa using length)⟩

def observationLoss (model : C → Runtime.TicketTable Bool) (pair : C × Bool) : ℝ :=
  Quality.brier (fun a => ((model pair.1).law a).toReal) pair.2

omit [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] in
theorem observationLoss_bounds (model : C → Runtime.TicketTable Bool) (pair : C × Bool) :
    observationLoss model pair ∈ Set.Icc (0 : ℝ) 2 := by
  constructor
  · exact Quality.brier_nonneg _ _
  · have hp (a : Bool) : 0 ≤ ((model pair.1).law a).toReal ∧
        ((model pair.1).law a).toReal ≤ 1 :=
      ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by norm_num)
        (by simpa using (model pair.1).law.coe_le_one a)⟩
    have squares (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : x^2 ≤ 1 ∧ (x-1)^2 ≤ 1 := by
      constructor <;> nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    have h0 := squares _ (hp false)
    have h1 := squares _ (hp true)
    rcases pair with ⟨c, b⟩
    cases b <;> simp [observationLoss, Quality.brier] <;> nlinarith

theorem integral_observationLoss (contexts : PMF C) (source : C → PMF Bool)
    (model : C → Runtime.TicketTable Bool) :
    ∫ pair, observationLoss model pair ∂(observationLaw contexts source).toMeasure =
      population contexts source model := by
  rw [PMF.integral_eq_sum, Fintype.sum_prod_type]
  simp only [observationLaw_apply, ENNReal.toReal_mul, smul_eq_mul, population, Quality.risk,
    Finset.mul_sum, observationLoss, mul_assoc]

omit [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] in
theorem sampled_empirical {n : Nat} [NeZero n] (sample : Fin n → C × Bool)
    (model : C → Runtime.TicketTable Bool) :
    (empirical (sampledValidation sample) model : ℝ) =
      (∑ i, observationLoss model (sample i)) / n := by
  rw [empirical_cast]
  simp [sampledValidation, List.map_ofFn, List.sum_ofFn, observationLoss]

theorem integral_coordinate_loss (n : Nat) (contexts : PMF C) (source : C → PMF Bool)
    (model : C → Runtime.TicketTable Bool) (i : Fin n) :
    ∫ sample, observationLoss model (sample i) ∂validationLaw n contexts source =
      population contexts source model := by
  unfold validationLaw
  rw [← integral_map (measurable_pi_apply i).aemeasurable
    (measurable_of_countable (observationLoss model)).aestronglyMeasurable]
  rw [(measurePreserving_eval (fun _ : Fin n => (observationLaw contexts source).toMeasure) i).map_eq]
  exact integral_observationLoss contexts source model

end
end VerifiedClassifier.Selection
