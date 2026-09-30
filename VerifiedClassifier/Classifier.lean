import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! A classifier predicts a distribution. Choosing or sampling a label is a
separate operation. No claim about calibration or data accuracy is assumed. -/

namespace VerifiedClassifier

universe u v w z

structure Classifier (Context : Type u) (Label : Type v)
    (Memory : Type w) (Program : Type z) where
  predict : Program → Memory → Context → PMF Label

namespace Classifier

variable {C : Type u} {L : Type v} {M : Type w} {P : Type z}

noncomputable def ofDeterministic (f : P → M → C → L) : Classifier C L M P :=
  ⟨fun p m c => PMF.pure (f p m c)⟩

/-- The output alphabet can be relabelled without changing the classifier. -/
noncomputable def mapLabels {K : Type*} (f : L → K)
    (classifier : Classifier C L M P) : Classifier C K M P :=
  ⟨fun p m c => (classifier.predict p m c).map f⟩

theorem total_mass (classifier : Classifier C L M P) (p : P) (m : M) (c : C) :
    ∑' label, classifier.predict p m c label = 1 := PMF.tsum_coe _

theorem probability_le_one (classifier : Classifier C L M P)
    (p : P) (m : M) (c : C) (label : L) :
    classifier.predict p m c label ≤ 1 := PMF.coe_le_one _ _

theorem deterministic_support (f : P → M → C → L) (p : P) (m : M) (c : C) :
    ((ofDeterministic f).predict p m c).support = {f p m c} := PMF.support_pure _

theorem mapLabels_support {K : Type*} (f : L → K)
    (classifier : Classifier C L M P) (p : P) (m : M) (c : C) :
    ((classifier.mapLabels f).predict p m c).support =
      f '' (classifier.predict p m c).support := PMF.support_map _ _

end Classifier

/-- A mode may not be unique; tie-breaking belongs to a decision rule. -/
def IsMode {L : Type*} (distribution : PMF L) (label : L) : Prop :=
  ∀ other, distribution other ≤ distribution label

/-- Finite nonempty label spaces always admit a most probable label. -/
theorem exists_mode {L : Type*} [Fintype L] [Nonempty L] (distribution : PMF L) :
    ∃ label, IsMode distribution label := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ distribution Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

/-- A sampler's correctness is a statement about its source law and pushforward.
This does not posit an executable exact-real random number generator. -/
def Samples {Seed L : Type*} (source : PMF Seed) (draw : Seed → L)
    (target : PMF L) : Prop := source.map draw = target

theorem samples_probability {Seed L : Type*} {source : PMF Seed}
    {draw : Seed → L} {target : PMF L} (h : Samples source draw target) (label : L) :
    (source.map draw) label = target label := congrArg (fun p : PMF L => p label) h

/-- The weighted probability of the returned labels is preserved by postprocessing. -/
theorem samples_map {Seed L K : Type*} {source : PMF Seed}
    {draw : Seed → L} {target : PMF L} (h : Samples source draw target) (f : L → K) :
    Samples source (f ∘ draw) (target.map f) := by
  unfold Samples at h ⊢
  rw [← PMF.map_comp, h]

end VerifiedClassifier
