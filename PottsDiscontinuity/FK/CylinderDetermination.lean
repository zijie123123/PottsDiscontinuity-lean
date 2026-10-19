/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxCylinders
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Determination by finite all-open cylinders

On the natural product measurable space of whole-lattice edge states, the
probability of every finite all-open cylinder determines the probability law.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open Set MeasureTheory
noncomputable section

namespace LatticeConfiguration

/-- The π-system of finite all-open cylinders. -/
def allOpenCylinders : Set (Set LatticeConfiguration) :=
  {s | ∃ F : Finset squareLattice.edgeSet, allOpen F = s}

theorem isPiSystem_allOpenCylinders : IsPiSystem allOpenCylinders := by
  intro s hs t ht hne
  rcases hs with ⟨F, rfl⟩
  rcases ht with ⟨G, rfl⟩
  refine ⟨F ∪ G, ?_⟩
  ext ω
  change (∀ e ∈ F ∪ G, ω e = true) ↔ (∀ e ∈ F, ω e = true) ∧
    (∀ e ∈ G, ω e = true)
  simp only [Finset.mem_union]
  constructor
  · intro h
    exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
  · rintro ⟨hF, hG⟩ e (he | he)
    · exact hF e he
    · exact hG e he

/-- Finite all-open cylinders generate the natural product σ-algebra. -/
theorem generateFrom_allOpenCylinders :
    MeasurableSpace.generateFrom allOpenCylinders =
      (MeasurableSpace.pi : MeasurableSpace (squareLattice.edgeSet → Bool)) := by
  classical
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le fun s hs => ?_
    rcases hs with ⟨F, rfl⟩
    induction F using Finset.induction_on with
    | empty => simp [allOpen]
    | @insert e F he ih =>
      rw [allOpen_insert]
      exact (measurable_pi_apply e (measurableSet_singleton true)).inter ih
  · rw [MeasurableSpace.pi]
    refine iSup_le fun e => ?_
    change MeasurableSpace.comap (fun ω : LatticeConfiguration => ω e)
      (inferInstance : MeasurableSpace Bool) ≤ MeasurableSpace.generateFrom allOpenCylinders
    let cylinderDeterminationGeneratedMeasurableSpace : MeasurableSpace LatticeConfiguration :=
      MeasurableSpace.generateFrom allOpenCylinders
    have hf : Measurable (fun ω : LatticeConfiguration => ω e) :=
      measurable_to_bool (by
        apply MeasurableSpace.measurableSet_generateFrom
        exact ⟨{e}, by ext ω; simp [allOpen]⟩)
    exact hf.comap_le

/-- Probability measures on the whole-lattice edge-state space are determined
by their values on every finite all-open cylinder. -/
theorem probabilityMeasure_eq_of_allOpen {μ ν : ProbabilityMeasure LatticeConfiguration}
    (h : ∀ F : Finset squareLattice.edgeSet,
      μ (allOpen F) = ν (allOpen F)) : μ = ν := by
  apply Subtype.ext
  let cylinderDeterminationProbabilityInstance :
    IsProbabilityMeasure (μ : Measure LatticeConfiguration) := μ.property
  have hfin : IsFiniteMeasure (μ : Measure LatticeConfiguration) := inferInstance
  exact @ext_of_generate_finite LatticeConfiguration (MeasurableSpace.pi)
    (μ : Measure LatticeConfiguration) (ν : Measure LatticeConfiguration)
    allOpenCylinders generateFrom_allOpenCylinders.symm isPiSystem_allOpenCylinders hfin
    (fun s hs => by
      rcases hs with ⟨F, rfl⟩
      rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure μ,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν]
      exact_mod_cast h F) (by simp)
end LatticeConfiguration
end
end PottsDiscontinuity.FK
