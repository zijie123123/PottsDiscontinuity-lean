module

public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Positive connection moments determine every finite connection pattern. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

variable {X I : Type*} [MeasurableSpace X]

/-- A finite pattern of required and forbidden relations. -/
def booleanEventPattern (E : I → Set X) (T C : Finset I) : Set X :=
  {x | (∀ i ∈ T, x ∈ E i) ∧ ∀ i ∈ C, x ∉ E i}

theorem booleanEventPattern_measurable (E : I → Set X) (hE : ∀ i, MeasurableSet (E i))
    (T C : Finset I) : MeasurableSet (booleanEventPattern E T C) := by
  have hT : {x | ∀ i ∈ T, x ∈ E i} = ⋂ i ∈ T, E i := by ext x; simp
  have hC : {x | ∀ i ∈ C, x ∉ E i} = ⋂ i ∈ C, (E i)ᶜ := by ext x; simp
  change MeasurableSet ({x | ∀ i ∈ T, x ∈ E i} ∩ {x | ∀ i ∈ C, x ∉ E i})
  rw [hT, hC]
  exact (T.measurableSet_biInter (fun i _ => hE i)).inter
    (C.measurableSet_biInter (fun i _ => (hE i).compl))

omit [MeasurableSpace X] in
theorem booleanEventPattern_insert (E : I → Set X) (T C : Finset I) (i : I) :
    booleanEventPattern E T (insert i C) =
      booleanEventPattern E T C \ booleanEventPattern E (insert i T) C := by
  ext x
  simp only [booleanEventPattern, Set.mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp,
    Set.mem_sdiff]
  tauto

/-- No uniqueness hypothesis is needed to recover the distribution of a finite
connection partition: all its positive moments suffice. -/
theorem boolean_pattern_probability_tendsto
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (E : ℕ → I → Set X) (Einf : I → Set X)
    (hE : ∀ n i, MeasurableSet (E n i)) (hEinf : ∀ i, MeasurableSet (Einf i))
    (hmom : ∀ T : Finset I,
      Tendsto (fun n => (μs n).toMeasure.real {x | ∀ i ∈ T, x ∈ E n i}) atTop
        (𝓝 (μ.toMeasure.real {x | ∀ i ∈ T, x ∈ Einf i})))
    (T C : Finset I) :
    Tendsto (fun n => (μs n).toMeasure.real (booleanEventPattern (E n) T C)) atTop
      (𝓝 (μ.toMeasure.real (booleanEventPattern Einf T C))) := by
  induction C using Finset.induction_on generalizing T with
  | empty => simpa only [booleanEventPattern, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
      and_true] using hmom T
  | @insert i C hi ih =>
      have ht := (ih T).sub (ih (insert i T))
      have hsub (E' : I → Set X) : booleanEventPattern E' (insert i T) C ⊆ booleanEventPattern E' T C := by
        intro x hx
        exact ⟨fun j hj => hx.1 j (Finset.mem_insert_of_mem hj), hx.2⟩
      have hn (n : ℕ) : (μs n).toMeasure.real (booleanEventPattern (E n) T (insert i C)) =
          (μs n).toMeasure.real (booleanEventPattern (E n) T C) -
            (μs n).toMeasure.real (booleanEventPattern (E n) (insert i T) C) := by
        rw [booleanEventPattern_insert, measureReal_sdiff (μ := (μs n).toMeasure)
          (hsub (E n)) (booleanEventPattern_measurable (E n) (hE n) _ _)]
      have hi' : μ.toMeasure.real (booleanEventPattern Einf T (insert i C)) =
          μ.toMeasure.real (booleanEventPattern Einf T C) -
            μ.toMeasure.real (booleanEventPattern Einf (insert i T) C) := by
        rw [booleanEventPattern_insert, measureReal_sdiff (μ := μ.toMeasure)
          (hsub Einf) (booleanEventPattern_measurable Einf hEinf _ _)]
      simp_rw [hn, hi']
      exact ht

end
end PottsDiscontinuity.Potts
