module

public import PottsDiscontinuity.RCInfinite.Cylinders
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.Trim

@[expose] public section

open MeasureTheory MeasurableSpace Set
open scoped symmDiff ENNReal

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- A cylinder whose finite support lies in the specified edge set. -/
def SupportedCylinder (E : Set Edge) (A : Set LatticeConfiguration) : Prop :=
  ∃ F : Finset Edge, (F : Set Edge) ⊆ E ∧ DependsOn (F : Set Edge) A

theorem SupportedCylinder.isCylinder {E : Set Edge} {A : Set LatticeConfiguration}
    (h : SupportedCylinder E A) : IsCylinder A := by
  obtain ⟨F, _, hF⟩ := h
  exact ⟨F, hF⟩

theorem SupportedCylinder.dependsOn {E : Set Edge} {A : Set LatticeConfiguration}
    (h : SupportedCylinder E A) : DependsOn E A := by
  obtain ⟨F, hFE, hF⟩ := h
  exact hF.mono hFE

theorem SupportedCylinder.compl {E : Set Edge} {A : Set LatticeConfiguration}
    (h : SupportedCylinder E A) : SupportedCylinder E Aᶜ := by
  obtain ⟨F, hFE, hF⟩ := h
  exact ⟨F, hFE, hF.compl⟩

theorem SupportedCylinder.union {E : Set Edge} {A B : Set LatticeConfiguration}
    (hA : SupportedCylinder E A) (hB : SupportedCylinder E B) : SupportedCylinder E (A ∪ B) := by
  obtain ⟨F, hFE, hF⟩ := hA
  obtain ⟨G, hGE, hG⟩ := hB
  refine ⟨F ∪ G, ?_, ?_⟩
  · simpa only [Finset.coe_union] using union_subset hFE hGE
  · intro ω η hω
    exact or_congr (hF ω η (fun e he => hω e (by simp [he])))
      (hG ω η (fun e he => hω e (by simp [he])))

theorem supportedCylinder_isSetAlgebra (E : Set Edge) :
    IsSetAlgebra {A | SupportedCylinder E A} where
  empty_mem := ⟨∅, by simp, fun _ _ _ => Iff.rfl⟩
  compl_mem := fun {_} h => h.compl
  union_mem := fun {_ _} hA hB => hA.union hB

/-- The sigma algebra of events which read only edges in `E`. -/
abbrev edgeSigma (E : Set Edge) : MeasurableSpace LatticeConfiguration :=
  generateFrom {A | SupportedCylinder E A}

theorem edgeSigma_le (E : Set Edge) :
    edgeSigma E ≤ (MeasurableSpace.pi : MeasurableSpace LatticeConfiguration) :=
  generateFrom_le fun _ h => h.isCylinder.measurableSet

def edgeProjection (E : Set Edge) (ω : LatticeConfiguration) : LatticeConfiguration :=
  fun e => if e ∈ E then ω e else false

theorem edgeProjection_measurable (E : Set Edge) :
    @Measurable LatticeConfiguration LatticeConfiguration (edgeSigma E) inferInstance
      (edgeProjection E) := by
  let : MeasurableSpace LatticeConfiguration := edgeSigma E
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e ∈ E
  · have hcoord : @Measurable LatticeConfiguration Bool (edgeSigma E) inferInstance
        (fun ω => ω e) := by
      apply measurable_to_bool
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨{e}, ?_, ?_⟩
      · simpa using he
      · intro ω η hω
        change ω e = true ↔ η e = true
        rw [hω e (by simp)]
    simpa only [edgeProjection, he, ite_true] using hcoord
  · simpa only [edgeProjection, he, ite_false] using
      (@measurable_const Bool LatticeConfiguration inferInstance (edgeSigma E) false)

theorem DependsOn.measurable_edgeSigma {E : Set Edge} {A : Set LatticeConfiguration}
    (hdep : DependsOn E A) (hA : MeasurableSet A) : MeasurableSet[edgeSigma E] A := by
  have heq : A = edgeProjection E ⁻¹' A := by
    ext ω
    exact hdep ω (edgeProjection E ω) (by
      intro e he
      simp only [edgeProjection, he, ite_true])
  rw [heq]
  exact edgeProjection_measurable E hA

/-- Approximation can preserve an arbitrary allowed set of coordinates. In
particular, an event independent of one edge admits independent cylinders as
approximants. -/
theorem exists_supportedCylinder_approx (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    (E : Set Edge) {A : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hdep : DependsOn E A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C, SupportedCylinder E C ∧ μ (C ∆ A) < ε := by
  have hAE : MeasurableSet[edgeSigma E] A := hdep.measurable_edgeSigma hA
  have hcover : ∃ D : Set (Set LatticeConfiguration), D.Countable ∧
      D ⊆ {C | SupportedCylinder E C} ∧ (μ.trim (edgeSigma_le E)) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, Set.countable_singleton _, ?_, by simp⟩
    intro C hC
    have hC' : C = univ := Set.mem_singleton_iff.mp hC
    subst C
    exact (supportedCylinder_isSetAlgebra E).univ_mem
  obtain ⟨C, hC, hCA⟩ := @exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    LatticeConfiguration (edgeSigma E) (μ.trim (edgeSigma_le E)) inferInstance
    {C | SupportedCylinder E C} (supportedCylinder_isSetAlgebra E).isSetRing
    hcover rfl A hAE ε hε
  refine ⟨C, hC, ?_⟩
  have hCE : MeasurableSet[edgeSigma E] C := MeasurableSpace.measurableSet_generateFrom hC
  rwa [trim_measurableSet_eq (edgeSigma_le E) (hCE.symmDiff hAE)] at hCA

theorem exists_cylinder_approx (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, IsCylinder C ∧ μ.real (C ∆ A) < ε := by
  obtain ⟨C, hC, hCA⟩ := exists_supportedCylinder_approx μ univ hA
    (fun ω η hω => by
      have hh : ω = η := funext fun e => hω e (mem_univ _)
      rw [hh]) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨C, hC.isCylinder, ?_⟩
  have ht := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hCA
  simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using ht

theorem abs_measureReal_sub_le_symmDiff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real A - μ.real B| ≤ μ.real (A ∆ B) := by
  have h := (MeasuredSets.lipschitzWith_measureReal (μ := μ)).dist_le_mul
    (⟨A, hA⟩ : MeasuredSets μ) (⟨B, hB⟩ : MeasuredSets μ)
  change |μ.real A - μ.real B| ≤ (1 : ℝ) * μ.real (A ∆ B) at h
  simpa only [one_mul] using h

end
end PottsDiscontinuity.RCInfinite
