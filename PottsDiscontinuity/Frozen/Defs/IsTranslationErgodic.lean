module

public import Mathlib

/-!
# Definition `IsTranslationErgodic` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- `μ` is invariant under every translation of `ℤ²`, and every measurable event invariant under
all translations of `ℤ²` is null or conull (ergodicity with respect to the translations of `ℤ²`). -/
def IsTranslationErgodic {S : Type*} [MeasurableSpace S] (μ : Measure (ℤ × ℤ → S)) : Prop :=
  (∀ a : ℤ × ℤ, μ.map (fun σ x => σ (x + a)) = μ) ∧
    ∀ s : Set (ℤ × ℤ → S), MeasurableSet s →
      (∀ a : ℤ × ℤ, (fun σ x => σ (x + a)) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0

end PottsDiscontinuity
