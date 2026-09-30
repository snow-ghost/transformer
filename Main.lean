import VerifiedClassifier.Example

open VerifiedClassifier

def main : IO Unit := do
  IO.println "Classes: 0, 1, 2; Laplace smoothing: one prior count per class"
  for a in List.finRange 3 do
    IO.println s!"P({a.val} | fruit) = {repr (Example.result.probabilities a)}"
  IO.println s!"Selected class: {Example.result.selected.val}"
  IO.println s!"Unseen context: P(0) = {repr (Example.unseen.probabilities 0)}; selected class = {Example.unseen.selected.val}"
