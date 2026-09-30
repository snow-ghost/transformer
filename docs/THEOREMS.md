# Theorem index

Every result below is included in `Checks.lean`. See the source for its complete hypotheses.

## ChoiceGuarantees

Source: [ChoiceGuarantees.lean](../VerifiedClassifier/ChoiceGuarantees.lean)

- `VerifiedClassifier.Choice.selected_maximal`
- `VerifiedClassifier.Choice.probabilities_correct`
- `VerifiedClassifier.Choice.probabilities_sum`
- `VerifiedClassifier.Choice.selected_mode`
- `VerifiedClassifier.Choice.matching_count`
- `VerifiedClassifier.Choice.learn_count`
- `VerifiedClassifier.Choice.learn_law`

## Classifier

Source: [Classifier.lean](../VerifiedClassifier/Classifier.lean)

- `VerifiedClassifier.Classifier.total_mass`
- `VerifiedClassifier.Classifier.probability_le_one`
- `VerifiedClassifier.Classifier.deterministic_support`
- `VerifiedClassifier.Classifier.mapLabels_support`
- `VerifiedClassifier.exists_mode`
- `VerifiedClassifier.samples_probability`
- `VerifiedClassifier.samples_map`

## Concentration

Source: [Concentration.lean](../VerifiedClassifier/Concentration.lean)

- `VerifiedClassifier.Selection.centered_loss_subgaussian`
- `VerifiedClassifier.Selection.centered_sum_subgaussian`
- `VerifiedClassifier.Selection.centered_sum_eq`
- `VerifiedClassifier.Selection.deviation_probability_le`
- `VerifiedClassifier.Selection.uniform_deviation_probability_le`

## Consistency

Source: [Consistency.lean](../VerifiedClassifier/Consistency.lean)

- `VerifiedClassifier.Frequency.smoothed_consistent`
- `VerifiedClassifier.Frequency.smoothed_risk_consistent`

## ExampleGuarantees

Source: [ExampleGuarantees.lean](../VerifiedClassifier/ExampleGuarantees.lean)

- `VerifiedClassifier.Example.prediction_law`
- `VerifiedClassifier.Example.decision_correct`

## Frequency

Source: [Frequency.lean](../VerifiedClassifier/Frequency.lean)

- `VerifiedClassifier.Frequency.count_observe`
- `VerifiedClassifier.Frequency.count_train`
- `VerifiedClassifier.Frequency.count_permutation`
- `VerifiedClassifier.Frequency.positive`
- `VerifiedClassifier.Frequency.probability_formula`
- `VerifiedClassifier.Frequency.permutation_invariant`
- `VerifiedClassifier.Frequency.observe_other_context`
- `VerifiedClassifier.Frequency.total_weight_observe`
- `VerifiedClassifier.Frequency.observed_probability_increases`

## Numerical

Source: [Numerical.lean](../VerifiedClassifier/Numerical.lean)

- `VerifiedClassifier.Numerical.expApprox_cast`
- `VerifiedClassifier.Numerical.expApprox_converges`
- `VerifiedClassifier.Numerical.expApprox_positive`
- `VerifiedClassifier.Numerical.softmaxApprox_cast`
- `VerifiedClassifier.Numerical.softmaxApprox_normalized`
- `VerifiedClassifier.Numerical.softmaxApprox_nonneg`
- `VerifiedClassifier.Numerical.softmaxApprox_converges`
- `VerifiedClassifier.Numerical.risk_converges`

## Quality

Source: [Quality.lean](../VerifiedClassifier/Quality.lean)

- `VerifiedClassifier.Quality.source_sum`
- `VerifiedClassifier.Quality.brier_nonneg`
- `VerifiedClassifier.Quality.risk_nonneg`
- `VerifiedClassifier.Quality.brier_expansion`
- `VerifiedClassifier.Quality.risk_expansion`
- `VerifiedClassifier.Quality.risk_decomposition`
- `VerifiedClassifier.Quality.truthful_minimizes`
- `VerifiedClassifier.Quality.risk_eq_minimum_iff`

## Rules

Source: [Rules.lean](../VerifiedClassifier/Rules.lean)

- `VerifiedClassifier.Rules.same_key`
- `VerifiedClassifier.Rules.recover`
- `VerifiedClassifier.Rules.sufficient_iff_factor`
- `VerifiedClassifier.Rules.compressed_risk_minimal`
- `VerifiedClassifier.Rules.approximation_cost`
- `VerifiedClassifier.Rules.observation_transfers`

## Runtime

Source: [Runtime.lean](../VerifiedClassifier/Runtime.lean)

- `VerifiedClassifier.Runtime.TicketTable.pick_mem`

## Sampling

Source: [Sampling.lean](../VerifiedClassifier/Sampling.lean)

- `VerifiedClassifier.Runtime.TicketTable.samples`
- `VerifiedClassifier.Runtime.count_as_sum`
- `VerifiedClassifier.Runtime.TicketTable.law_formula`
- `VerifiedClassifier.Runtime.TicketTable.rational_probability`
- `VerifiedClassifier.Runtime.matching_count`
- `VerifiedClassifier.Runtime.learnBool_count`
- `VerifiedClassifier.Runtime.bool_count_total`
- `VerifiedClassifier.Runtime.learnBool_law`

## Selection

Source: [Selection.lean](../VerifiedClassifier/Selection.lean)

- `VerifiedClassifier.Selection.best_mem`
- `VerifiedClassifier.Selection.bestMeasured_value`
- `VerifiedClassifier.Selection.bestMeasured_calls`

## SelectionGuarantees

Source: [SelectionGuarantees.lean](../VerifiedClassifier/SelectionGuarantees.lean)

- `VerifiedClassifier.Selection.best_le`
- `VerifiedClassifier.Selection.select_mem`
- `VerifiedClassifier.Selection.select_optimal`
- `VerifiedClassifier.Selection.cost_antitone`
- `VerifiedClassifier.Selection.loss_cast`
- `VerifiedClassifier.Selection.empirical_cast`
- `VerifiedClassifier.Selection.fit_law`
- `VerifiedClassifier.Selection.population_decomposition`
- `VerifiedClassifier.Selection.oracle_bound`
- `VerifiedClassifier.Selection.selects_of_gap`
- `VerifiedClassifier.Selection.excess_risk_bound`

## StatisticalSelection

Source: [StatisticalSelection.lean](../VerifiedClassifier/StatisticalSelection.lean)

- `VerifiedClassifier.Selection.confidenceRadius_pos`
- `VerifiedClassifier.Selection.failure_at_radius`
- `VerifiedClassifier.Selection.confidenceRadius_le_of_sample_size`
- `VerifiedClassifier.Selection.accuracy_probability_ge`
- `VerifiedClassifier.Selection.accuracy_probability_of_sample_size`
- `VerifiedClassifier.Selection.selection_probability_ge`
- `VerifiedClassifier.Selection.excess_risk_probability_ge`

## Temperature

Source: [Temperature.lean](../VerifiedClassifier/Temperature.lean)

- `VerifiedClassifier.FiniteWeights.probability_nonneg`
- `VerifiedClassifier.FiniteWeights.probability_sum`
- `VerifiedClassifier.FiniteWeights.probability_le_one`
- `VerifiedClassifier.FiniteWeights.probability_le_iff`
- `VerifiedClassifier.FiniteWeights.toPMF_apply`
- `VerifiedClassifier.FiniteWeights.toPMF_le_iff`
- `VerifiedClassifier.FiniteWeights.toPMF_toReal`
- `VerifiedClassifier.Softmax.probability_formula`
- `VerifiedClassifier.Softmax.normalized`
- `VerifiedClassifier.Softmax.order_iff`
- `VerifiedClassifier.Softmax.mode_iff`
- `VerifiedClassifier.Softmax.modes_temperature_independent`
- `VerifiedClassifier.Softmax.odds_formula`
- `VerifiedClassifier.Softmax.colder_odds`
- `VerifiedClassifier.Softmax.positive`
- `VerifiedClassifier.Softmax.support_full`
- `VerifiedClassifier.Softmax.unit_temperature`

## ValidationSampling

Source: [ValidationSampling.lean](../VerifiedClassifier/ValidationSampling.lean)

- `VerifiedClassifier.Selection.observationLaw_apply`
- `VerifiedClassifier.Selection.observationLoss_bounds`
- `VerifiedClassifier.Selection.integral_observationLoss`
- `VerifiedClassifier.Selection.sampled_empirical`
- `VerifiedClassifier.Selection.integral_coordinate_loss`

