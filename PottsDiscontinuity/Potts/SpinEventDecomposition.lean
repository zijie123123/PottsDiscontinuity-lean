module

public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section

/-- Equality of two finite-valued spins is the disjoint sum over their common colour. -/
theorem measureReal_same_colour_sum {X C : Type*} [MeasurableSpace X] [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → C) (hf : Measurable f) (hg : Measurable g) :
    μ.real {x | f x = g x} = ∑ c : C, μ.real {x | f x = c ∧ g x = c} := by
  have he : {x | f x = g x} = ⋃ c ∈ (Finset.univ : Finset C), {x | f x = c ∧ g x = c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and]
    constructor
    · intro h
      exact ⟨f x, rfl, h.symm⟩
    · rintro ⟨c, hf, hg⟩
      exact hf.trans hg.symm
  have hd : (↑(Finset.univ : Finset C) : Set C).PairwiseDisjoint
      (fun c => {x | f x = c ∧ g x = c}) := by
    intro c _ d _ hcd
    change Disjoint {x | f x = c ∧ g x = c} {x | f x = d ∧ g x = d}
    rw [Set.disjoint_left]
    intro x hc hd
    exact hcd (hc.1.symm.trans hd.1)
  rw [he]
  exact measureReal_biUnion_finset hd (fun c _ =>
    (hf (measurableSet_singleton c)).inter (hg (measurableSet_singleton c)))

end
end PottsDiscontinuity.Potts
