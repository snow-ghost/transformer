# Verified probabilistic classifier

A standalone Lean 4 formalization of a probabilistic classifier with memory,
a configurable program, temperature, supervised learning, and a most-probable
class decision. Includes an executable three-class example and kernel-checked
proofs relating the implementation to its probability model.

[Русское описание](README.ru.md) · [Theorem index](docs/THEOREMS.md) · [MIT license](LICENSE)

This is a **Jev-inspired classification interface**, not a verified implementation
of Jev. No correspondence theorem for Jev internals, neural-network training, or
Transformer attention is claimed. The repository's directory name does not
change that scope.

## Build and run

Install `elan` and Python 3, then run from the repository root:

```sh
python3 scripts/fetch_cache.py
lake build
python3 scripts/check.py
lake exe classifierDemo
```

`lean-toolchain` pins **Lean 4.34.0**. Mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435`; `lake-manifest.json` pins all transitive
dependencies. Cache retrieval requires network access on the first setup.
Warnings are errors and implicit variable declaration is disabled.

The demo learns from four observations of class 0 and one of class 1 for the
same context. An observation for a different context does not affect that row.
With one prior count per class:

| Class | Probability |
|---|---:|
| 0 | 5/8 |
| 1 | 1/4 |
| 2 | 1/8 |

The selected class is 0. An unseen context has probabilities 1/3 for all three
classes; the deterministic tie rule selects class 0. These values are checked
by Lean, not only printed by the executable.

## Model and results

The general interface is:

```lean
structure Classifier (Context Label Memory Program : Type) where
  predict : Program → Memory → Context → PMF Label
```

The source declaration is universe-polymorphic. `PMF` is a discrete probability
mass function from Mathlib. Context, memory, and program types are abstract;
the finite-label assumption is introduced where required.

| Component | Main guarantees |
|---|---|
| `Classifier` | Total probability is 1; deterministic embedding; label mapping; existence of a mode for finite nonempty labels |
| `Temperature` | Nonnegative-weight normalization; softmax positivity; score order and modes preserved for positive temperature; relative-odds formula |
| `Frequency` | Smoothed conditional frequencies; permutation invariance; other contexts preserved; an observation increases its own label's probability |
| `Rules` | Feature-based memory; exact recovery when the feature is sufficient for the source law |
| `Quality` | Brier-risk decomposition; the true distribution uniquely minimizes expected Brier loss |
| `Consistency` | Smoothed probabilities and risk converge **if** rescaled empirical counts converge appropriately |
| `Sampling`, `Numerical` | Exact ticket probabilities; executable rational learner correspondence; conditional convergence of rational exponential/softmax approximations |
| `Selection`, `SelectionGuarantees` | Exhaustive finite selection; empirical optimality; oracle bounds under accurate risk estimates |
| `ValidationSampling`, `Concentration`, `StatisticalSelection` | Fresh IID validation guarantees and an explicit sample-size/error/failure tradeoff for a fixed finite binary-classifier catalogue |
| `Choice`, `ChoiceGuarantees` | Executable multiclass Laplace learner; reported probabilities agree with its law; selected label is a mode |

For a nonempty finite label set and positive smoothing α, the learned row is

\[
p(a\mid c)=\frac{N(c,a)+\alpha}{\sum_b N(c,b)+|L|\alpha}.
\]

The executable `Choice.learn` uses α = 1 and classes `Fin k`, with `k > 0`.
`Choice.choose` returns both rational probabilities and a maximizing label.
It retains the first maximum in `0 :: List.finRange k`. Temperature affects
softmax probabilities while preserving its set of modes; it does not by itself
make the argmax decision random. Sampling is a separate operation.

## Assumptions and boundaries

- Normalization is a mathematical property of a forecast, not evidence that its
  probabilities match an unknown real-world source or are calibrated.
- Feature-based recovery requires identical source distributions for contexts
  sharing a feature. Conditional consistency explicitly assumes convergence of
  empirical counts; arbitrary data do not satisfy this automatically.
- Statistical selection results in this extraction concern **binary** labels,
  finite context spaces, a fixed finite candidate catalogue, and fresh IID
  validation data. The core classifier, softmax, frequency learner and `Choice`
  support multiple classes. Multiclass statistical selection is not claimed.
- Real softmax is mathematical semantics. The rational approximation results
  have their own hypotheses (including nonnegative scaled scores for the
  supplied positivity guarantee); they are not a `Float` error certificate.
- Exact ticket sampling assumes a uniform source index. `IO.rand` and its
  independence are outside these proofs. The demonstration uses no randomness.
- Program-memory evolution, generative machines, termination, and the larger
  experimental architecture are outside this standalone package.

## Proof audit and contributions

There are **106 named theorems and 5 computational examples**. `lake build`
checks all library modules and examples. `Checks.lean` lists every named theorem;
`scripts/check.py` verifies that the list is complete and that the reported
axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
The source audit rejects `sorry`, `admit`, new `axiom` declarations, `unsafe`
and `native_decide`. Computational examples use kernel reduction.

GitHub Actions runs the build, theorem audit and demonstration. When extending
the library, state hypotheses explicitly, add new theorem names to `Checks.lean`
in module/declaration order, and run the same commands locally. See
[extraction provenance](docs/PROVENANCE.md) for the source subset and adaptations.

## License

Project sources and documentation are available under the [MIT license](LICENSE).
Mathlib, Lean and other dependencies retain their own licenses. Downloaded
packages and build outputs live in the ignored `.lake/` directory.
