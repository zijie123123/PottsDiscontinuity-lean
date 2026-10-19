module

public import PottsDiscontinuity.RCInfinite.BoxExhaustion

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK

abbrev Edge := squareLattice.edgeSet

/-- An event reads only the coordinates in `E`. The set `E` need not be finite. -/
def DependsOn (E : Set Edge) (A : Set LatticeConfiguration) : Prop :=
  ∀ ω η, (∀ e ∈ E, ω e = η e) → (ω ∈ A ↔ η ∈ A)

/-- A finite-coordinate event on the original lattice edges. -/
def IsCylinder (A : Set LatticeConfiguration) : Prop :=
  ∃ F : Finset Edge, DependsOn (F : Set Edge) A

theorem DependsOn.mono {E F : Set Edge} {A : Set LatticeConfiguration}
    (h : DependsOn E A) (hEF : E ⊆ F) : DependsOn F A :=
  fun ω η hω => h ω η (fun e he => hω e (hEF he))

theorem DependsOn.compl {E : Set Edge} {A : Set LatticeConfiguration}
    (h : DependsOn E A) : DependsOn E Aᶜ := by
  intro ω η hω
  exact not_congr (h ω η hω)

theorem DependsOn.inter {E F : Set Edge} {A B : Set LatticeConfiguration}
    (hA : DependsOn E A) (hB : DependsOn F B) : DependsOn (E ∪ F) (A ∩ B) := by
  intro ω η hω
  exact and_congr (hA ω η (fun e he => hω e (Or.inl he)))
    (hB ω η (fun e he => hω e (Or.inr he)))

theorem IsCylinder.compl {A : Set LatticeConfiguration} (h : IsCylinder A) :
    IsCylinder Aᶜ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, hF.compl⟩

theorem IsCylinder.inter {A B : Set LatticeConfiguration}
    (hA : IsCylinder A) (hB : IsCylinder B) : IsCylinder (A ∩ B) := by
  obtain ⟨E, hE⟩ := hA
  obtain ⟨F, hF⟩ := hB
  exact ⟨E ∪ F, by simpa using hE.inter hF⟩

theorem isCylinder_coordinate (e : Edge) (b : Bool) :
    IsCylinder {ω : LatticeConfiguration | ω e = b} := by
  refine ⟨{e}, ?_⟩
  intro ω η hω
  change ω e = b ↔ η e = b
  rw [hω e (by simp)]

theorem isCylinder_allOpen (F : Finset Edge) :
    IsCylinder (LatticeConfiguration.allOpen F) := by
  refine ⟨F, ?_⟩
  intro ω η hω
  change (∀ e ∈ F, ω e = true) ↔ (∀ e ∈ F, η e = true)
  constructor <;> intro h e he
  · rw [← hω e he]; exact h e he
  · rw [hω e he]; exact h e he

theorem IsCylinder.isClopen {A : Set LatticeConfiguration} (hA : IsCylinder A) :
    IsClopen A := by
  classical
  obtain ⟨F, hF⟩ := hA
  let restrict : LatticeConfiguration → (F → Bool) := fun ω e => ω e
  let extend : (F → Bool) → LatticeConfiguration :=
    fun ξ e => if he : e ∈ F then ξ ⟨e, he⟩ else false
  have hcont : Continuous restrict := continuous_pi fun e => continuous_apply e.val
  have heq : A = restrict ⁻¹' (extend ⁻¹' A) := by
    ext ω
    exact hF ω (extend (restrict ω)) (by
      intro e he
      have he' : e ∈ F := he
      simp [extend, restrict, he'])
  rw [heq]
  exact (isClopen_discrete (extend ⁻¹' A)).preimage hcont

theorem IsCylinder.measurableSet {A : Set LatticeConfiguration} (hA : IsCylinder A) :
    MeasurableSet A := hA.isClopen.isOpen.measurableSet

/-- The two actual finite-box laws, with their respective exterior extensions. -/
noncomputable def boxMeasure (θ : Parameters) (i : Fin 2) (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure LatticeConfiguration :=
  if i = 0 then boxProbabilityMeasure θ c r else wiredBoxProbabilityMeasure θ c r

@[simp] theorem boxMeasure_free (θ : Parameters) (c : LatticeVertex) (r : ℕ) :
    boxMeasure θ 0 c r = boxProbabilityMeasure θ c r := by simp [boxMeasure]

@[simp] theorem boxMeasure_wired (θ : Parameters) (c : LatticeVertex) (r : ℕ) :
    boxMeasure θ 1 c r = wiredBoxProbabilityMeasure θ c r := by simp [boxMeasure]

theorem boxMeasure_tendsto (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    Tendsto (fun n => boxMeasure θ i (0, 0) n) atTop
      (𝓝 (⟨μ, hμ.1⟩ : ProbabilityMeasure LatticeConfiguration)) := by
  fin_cases i
  · simpa using free_box_exhaustion θ μ hμ (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
  · simpa using wired_box_exhaustion θ μ hμ (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive

theorem tendsto_cylinder_probability (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    {A : Set LatticeConfiguration} (hA : IsCylinder A) :
    Tendsto (fun n => (boxMeasure θ i (0, 0) n : Measure LatticeConfiguration).real A)
      atTop (𝓝 (μ.real A)) := by
  have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (boxMeasure_tendsto θ i μ hμ) hA.isClopen
  simpa [ProbabilityMeasure.coeFn_def, Measure.real, ENNReal.toReal, Function.comp_def] using
    (NNReal.continuous_coe.tendsto _).comp h

end PottsDiscontinuity.RCInfinite
