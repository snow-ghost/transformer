# Extraction provenance

This package was extracted from the larger `SymbolicSystem` Lean research
workspace. The following original modules were retained:

`Classifier`, `Temperature`, `Quality`, `Frequency`, `Consistency`, `Rules`,
`Runtime`, `Sampling`, `Numerical`, `Selection`, `SelectionGuarantees`,
`ValidationSampling`, `Concentration`, `StatisticalSelection`.

Their namespace and local imports were changed from `SymbolicSystem` to
`VerifiedClassifier`. The unused `Prediction` import was removed from
`Classifier`, eliminating dependencies on the generative machine and its core.
Apart from these substitutions, the extracted module text is unchanged.
The extracted proofs were rebuilt in this standalone package.

`Choice`, `ChoiceGuarantees`, `Example`, and `ExampleGuarantees` were added during
extraction to provide a direct multiclass probability-and-decision interface,
prove its relation to the retained frequency model, and demonstrate its use.
The executable demonstration, full axiom audit and CI configuration belong to
this standalone package.

No Jev implementation, model weights or training data were imported. No theorem
identifies these algorithms with Jev internals. The original research workspace
remains intact; this extraction owns its own source files and pinned dependency
manifest and requires no import from that workspace.

Third-party dependencies are referenced through Lake rather than included in
the source release. Their downloaded copies and cached artifacts are excluded
by `.gitignore`.
