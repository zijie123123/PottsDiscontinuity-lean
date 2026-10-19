module

public import PottsDiscontinuity.RCInfinite.MeasurableBounds

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- Prescribe one edge state, retaining all other original edge states. -/
def setEdge (e : Edge) (b : Bool) (ω : LatticeConfiguration) : LatticeConfiguration :=
  fun f => if f = e then b else ω f

@[simp] theorem setEdge_self (e : Edge) (b : Bool) (ω : LatticeConfiguration) :
    setEdge e b ω e = b := by simp [setEdge]

@[simp] theorem setEdge_setEdge (e : Edge) (b c : Bool) (ω : LatticeConfiguration) :
    setEdge e b (setEdge e c ω) = setEdge e b ω := by
  funext f
  by_cases hf : f = e <;> simp [setEdge, hf]

theorem setEdge_eq_self (e : Edge) (b : Bool) (ω : LatticeConfiguration) (h : ω e = b) :
    setEdge e b ω = ω := by
  funext f
  by_cases hf : f = e <;> simp [setEdge, hf, h]

theorem setEdge_measurable (e : Edge) (b : Bool) : Measurable (setEdge e b) := by
  apply measurable_pi_iff.mpr
  intro f
  by_cases hf : f = e
  · simpa only [setEdge, hf, ite_true] using (measurable_const (a := b) :
      Measurable (fun _ : LatticeConfiguration => b))
  · simpa only [setEdge, hf, ite_false] using measurable_pi_apply f

/-- The event obtained by forgetting the value of one edge. -/
def edgeSaturation (e : Edge) (A : Set LatticeConfiguration) : Set LatticeConfiguration :=
  (setEdge e false) ⁻¹' A ∪ (setEdge e true) ⁻¹' A

theorem edgeSaturation_measurable (e : Edge) {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    MeasurableSet (edgeSaturation e A) :=
  ((setEdge_measurable e false) hA).union ((setEdge_measurable e true) hA)

theorem edgeSaturation_dependsOn (e : Edge) (A : Set LatticeConfiguration) :
    DependsOn ({e}ᶜ) (edgeSaturation e A) := by
  intro ω η hω
  have heq (b : Bool) : setEdge e b ω = setEdge e b η := by
    funext f
    by_cases hf : f = e
    · simp [setEdge, hf]
    · simp only [setEdge, hf, ite_false]
      exact hω f (by simpa using hf)
  change (setEdge e false ω ∈ A ∨ setEdge e true ω ∈ A) ↔
    (setEdge e false η ∈ A ∨ setEdge e true η ∈ A)
  rw [heq false, heq true]

theorem subset_edgeSaturation (e : Edge) (A : Set LatticeConfiguration) : A ⊆ edgeSaturation e A := by
  intro ω hω
  cases h : ω e
  · left
    change setEdge e false ω ∈ A
    rwa [setEdge_eq_self e false ω h]
  · right
    change setEdge e true ω ∈ A
    rwa [setEdge_eq_self e true ω h]

theorem setEdge_image (e : Edge) (b : Bool) (A : Set LatticeConfiguration) :
    setEdge e b '' A = edgeSaturation e A ∩ {ω | ω e = b} := by
  ext ω
  constructor
  · rintro ⟨η, hη, rfl⟩
    refine ⟨?_, by simp⟩
    cases h : η e
    · left
      change setEdge e false (setEdge e b η) ∈ A
      rwa [setEdge_setEdge, setEdge_eq_self e false η h]
    · right
      change setEdge e true (setEdge e b η) ∈ A
      rwa [setEdge_setEdge, setEdge_eq_self e true η h]
  · rintro ⟨hω, hb⟩
    rcases hω with hω | hω
    · refine ⟨setEdge e false ω, hω, ?_⟩
      rw [setEdge_setEdge, setEdge_eq_self e b ω hb]
    · refine ⟨setEdge e true ω, hω, ?_⟩
      rw [setEdge_setEdge, setEdge_eq_self e b ω hb]

theorem measurableSet_setEdge_image (e : Edge) (b : Bool)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) : MeasurableSet (setEdge e b '' A) := by
  rw [setEdge_image]
  exact (edgeSaturation_measurable e hA).inter (isCylinder_coordinate e b).measurableSet

theorem setEdge_image_energy (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (e : Edge) (b : Bool) {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    energyBound θ * μ.real A ≤ μ.real (setEdge e b '' A) := by
  have : IsProbabilityMeasure μ := hμ.1
  rw [setEdge_image]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (subset_edgeSaturation e A))
    (energyBound_pos θ).le).trans
      (measurable_finite_energy_uniform θ i μ hμ e (edgeSaturation_measurable e hA)
        (edgeSaturation_dependsOn e A) b)

/-- Prescribe exactly the states in a finite edge set. -/
def setEdges (F : Finset Edge) (ξ : Edge → Bool) (ω : LatticeConfiguration) : LatticeConfiguration :=
  fun e => if e ∈ F then ξ e else ω e

@[simp] theorem setEdges_empty (ξ : Edge → Bool) : setEdges ∅ ξ = id := by
  funext ω e
  simp [setEdges]

theorem setEdges_insert (e : Edge) (F : Finset Edge) (ξ : Edge → Bool) :
    setEdges (insert e F) ξ = setEdge e (ξ e) ∘ setEdges F ξ := by
  funext ω f
  by_cases hf : f = e <;> simp [setEdges, setEdge, hf]

theorem measurableSet_setEdges_image (F : Finset Edge) (ξ : Edge → Bool)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) : MeasurableSet (setEdges F ξ '' A) := by
  induction F using Finset.induction_on with
  | empty => simpa only [setEdges_empty, Set.image_id] using hA
  | insert e F he ih =>
    rw [setEdges_insert]
    simp only [Function.comp_def]
    rw [← Set.image_image (setEdge e (ξ e)) (setEdges F ξ) A]
    exact measurableSet_setEdge_image e (ξ e) ih

/-- Quantitative finite-energy surgery. In particular every prescribed finite
modification of a positive-measure measurable event still has positive measure. -/
theorem setEdges_image_energy (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) (ξ : Edge → Bool) {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    energyBound θ ^ F.card * μ.real A ≤ μ.real (setEdges F ξ '' A) := by
  induction F using Finset.induction_on with
  | empty => simp only [Finset.card_empty, pow_zero, one_mul, setEdges_empty, Set.image_id, le_refl]
  | insert e F he ih =>
    rw [Finset.card_insert_of_notMem he, setEdges_insert]
    simp only [Function.comp_def]
    rw [← Set.image_image (setEdge e (ξ e)) (setEdges F ξ) A]
    calc
      energyBound θ ^ (F.card + 1) * μ.real A =
          energyBound θ * (energyBound θ ^ F.card * μ.real A) := by ring
      _ ≤ energyBound θ * μ.real (setEdges F ξ '' A) :=
        mul_le_mul_of_nonneg_left ih (energyBound_pos θ).le
      _ ≤ μ.real (setEdge e (ξ e) '' (setEdges F ξ '' A)) :=
        setEdge_image_energy θ i μ hμ e (ξ e) (measurableSet_setEdges_image F ξ hA)

theorem setEdges_image_real_pos (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) (ξ : Edge → Bool) {A : Set LatticeConfiguration}
    (hA : MeasurableSet A) (hpos : 0 < μ.real A) : 0 < μ.real (setEdges F ξ '' A) :=
  (mul_pos (pow_pos (energyBound_pos θ) _) hpos).trans_le (setEdges_image_energy θ i μ hμ F ξ hA)

end
end PottsDiscontinuity.RCInfinite
