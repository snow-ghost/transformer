import VerifiedClassifier.Example
import VerifiedClassifier.ChoiceGuarantees

namespace VerifiedClassifier.Example

example : result.probabilities 0 = (5/8 : Rat) := by decide +kernel
example : result.probabilities 1 = (1/4 : Rat) := by decide +kernel
example : result.probabilities 2 = (1/8 : Rat) := by decide +kernel
example : result.selected = 0 := by decide +kernel
example : unseen.probabilities 0 = (1/3 : Rat) ∧ unseen.selected = 0 := by decide +kernel

theorem prediction_law : (Choice.learn data "fruit").law = Frequency.predict data Frequency.laplace "fruit" :=
  Choice.learn_law _ _

theorem decision_correct : IsMode (Choice.learn data "fruit").law result.selected := Choice.selected_mode _

end VerifiedClassifier.Example
