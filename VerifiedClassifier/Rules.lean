import VerifiedClassifier.Frequency

namespace VerifiedClassifier
namespace Rules

noncomputable section
variable {C R L : Type*}

/-- Contexts may share a rule precisely when the source law agrees on each fibre. -/
def Sufficient (source : C → PMF L) (key : C → R) : Prop :=
  ∀ c d, key c = key d → source c = source d

/-- The program extracts a feature; memory stores a distribution for each feature. -/
def classifier : Classifier C L (R → PMF L) (C → R) := ⟨fun key memory c => memory (key c)⟩

theorem same_key (key : C → R) (memory : R → PMF L) {c d : C} (h : key c = key d) :
    classifier.predict key memory c = classifier.predict key memory d := congrArg memory h

def compress (source : C → PMF L) (key : C → R) (covers : Function.Surjective key) : R → PMF L :=
  fun r => source (Classical.choose (covers r))

theorem recover (source : C → PMF L) (key : C → R) (covers : Function.Surjective key)
    (sufficient : Sufficient source key) (c : C) :
    compress source key covers (key c) = source c :=
  sufficient _ c (Classical.choose_spec (covers (key c)))

theorem sufficient_iff_factor (source : C → PMF L) (key : C → R)
    (covers : Function.Surjective key) :
    Sufficient source key ↔ ∃ memory : R → PMF L, ∀ c, memory (key c) = source c := by
  constructor
  · intro h
    exact ⟨compress source key covers, recover source key covers h⟩
  · rintro ⟨memory, h⟩ c d same
    rw [← h c, ← h d, same]

theorem compressed_risk_minimal [Fintype L] [DecidableEq L]
    (source : C → PMF L) (key : C → R) (covers : Function.Surjective key)
    (sufficient : Sufficient source key) (c : C) (other : L → ℝ) :
    Quality.risk (source c) (fun a => (compress source key covers (key c) a).toReal) ≤
      Quality.risk (source c) other := by
  rw [recover source key covers sufficient c]
  exact Quality.truthful_minimizes _ _

/-- Approximate rules have an exactly quantified excess Brier risk. -/
theorem approximation_cost [Fintype L] [DecidableEq L]
    (source : C → PMF L) (key : C → R) (memory : R → PMF L) (c : C) :
    Quality.risk (source c) (fun a => (memory (key c) a).toReal) =
      Quality.risk (source c) (fun a => (source c a).toReal) +
      Quality.squaredDistance (fun a => (source c a).toReal) (fun a => (memory (key c) a).toReal) :=
  Quality.risk_decomposition _ _

def encodeData (key : C → R) (data : Frequency.Data C L) : Frequency.Data R L :=
  data.map (fun pair => (key pair.1, pair.2))

variable [DecidableEq R] [DecidableEq L] [Fintype L] [Nonempty L]

def learned (key : C → R) (data : Frequency.Data C L) (α : Frequency.Smoothing) (c : C) : PMF L :=
  Frequency.predict (encodeData key data) α (key c)

/-- One observation is shared with every context mapped to the same rule. -/
theorem observation_transfers (key : C → R) (data : Frequency.Data C L) (α : Frequency.Smoothing)
    (c d : C) (a : L) (same : key c = key d) :
    (learned key data α d a).toReal ≤ (learned key ((c, a) :: data) α d a).toReal := by
  unfold learned encodeData
  simp only [List.map_cons, same]
  exact Frequency.observed_probability_increases _ α (key d) a

end
end Rules
end VerifiedClassifier
