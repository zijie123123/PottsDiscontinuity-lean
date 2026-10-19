module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.Box
public import PottsDiscontinuity.Frozen.Defs.PottsProb

/-!
# Definition `IsPottsInfiniteVolumeLimit` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

open Classical in
/-- `μ` is the infinite-volume Potts Gibbs measure `μⁱ_β`: the probability measure on
`{1,…,q}^{ℤ²}` to which `μⁱ_{Λₙ,β}` converge, tested on all finite-dimensional cylinder events.
The finite volumes are the boxes `Λₙ` (author ruling R1); the Hamiltonian is the paper's literal
one, with one boundary term per vertex of `∂Λₙ`. -/
def IsPottsInfiniteVolumeLimit (q : ℕ) (β : ℝ) (i : Fin (q + 1))
    (μ : Measure (ℤ × ℤ → Set.Icc 1 q)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (A : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Set.Icc 1 q),
      Tendsto
        (fun n : ℕ =>
          ∑ σ : ↥(box n : Set (ℤ × ℤ)) → Set.Icc 1 q,
            if ∀ x ∈ A, ∃ h : x ∈ box n, σ ⟨x, h⟩ = ξ x
            then pottsProb q (box n) β i σ else 0)
        atTop (𝓝 (μ.real {σ | ∀ x ∈ A, σ x = ξ x}))

end PottsDiscontinuity
