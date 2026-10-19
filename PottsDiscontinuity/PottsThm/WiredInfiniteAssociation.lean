module

public import PottsDiscontinuity.PottsThm.WiredAssociation
public import PottsDiscontinuity.Potts.WiredConnectionEvents
public import PottsDiscontinuity.Potts.MonotoneEventLimits
public import PottsDiscontinuity.RCInfinite.ClusterEvents

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

def wiredEscapeApprox (x : LatticeVertex) (n : ℕ) : Set LatticeConfiguration :=
  wiredDataEvent n {(some x, none)}

private theorem rcInfiniteOpenGraph_mono {ω η : LatticeConfiguration} (hωη : ω ≤ η) :
    rcInfiniteOpenGraph ω ≤ rcInfiniteOpenGraph η := by
  intro x y hxy
  rw [rcInfiniteOpenGraph_adj] at hxy ⊢
  obtain ⟨hedge, hopen⟩ := hxy
  have hη : η ⟨s(x, y), hedge⟩ = true := by
    have hle := hωη ⟨s(x, y), hedge⟩
    by_cases h : η ⟨s(x, y), hedge⟩ = true
    · exact h
    · have hf : η ⟨s(x, y), hedge⟩ = false := by
        cases hval : η ⟨s(x, y), hedge⟩ <;> simp_all
      exfalso
      exact (by decide : ¬ ((true : Bool) ≤ false)) (by simpa [hopen, hf] using hle)
  exact ⟨hedge, hη⟩

private theorem wiredEscapeApprox_upper (x : LatticeVertex) (n : ℕ) :
    IsUpperSet (wiredEscapeApprox x n) := by
  intro ω η hωη hω
  change ∀ z : Option LatticeVertex × Option LatticeVertex,
    z ∈ ({(some x, none)} : Finset (Option LatticeVertex × Option LatticeVertex)) →
    localWiredSetoid (rcInfiniteOpenGraph ω) n z.1 z.2 at hω
  change ∀ z : Option LatticeVertex × Option LatticeVertex,
    z ∈ ({(some x, none)} : Finset (Option LatticeVertex × Option LatticeVertex)) →
    localWiredSetoid (rcInfiniteOpenGraph η) n z.1 z.2
  intro z hz
  exact localWiredSetoid_mono (rcInfiniteOpenGraph_mono hωη) n (hω z hz)

private theorem wiredEscapeApprox_iInter (x : LatticeVertex) :
    (⋂ n, wiredEscapeApprox x n) = infiniteAt x := by
  change (⋂ n, wiredDataEvent n {(some x, none)}) = _
  rw [iInter_wiredDataEvent]
  ext ω
  simp [infiniteMergedDataEvent, infiniteMergedSetoid_some_none, RCInfinite.infiniteAt, cluster]
  rfl

private theorem wiredEscapeApprox_antitone (x : LatticeVertex) :
    Antitone (wiredEscapeApprox x) := by
  intro m n hmn
  exact wiredDataEvent_antitone _ hmn

private theorem wiredEscapeApprox_measurable (x : LatticeVertex) (n : ℕ) :
    MeasurableSet (wiredEscapeApprox x n) :=
  (wiredDataEvent_isClopen n _).2.measurableSet

/-- Whole-plane wired infinite-cluster events are positively associated in any
actual wired box limit. The finite wired connection events decrease to the
infinite-cluster events, so the clopen FKG inequality passes to their limit. -/
theorem wired_infinite_at_positive_association (θ : Parameters)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 φ))
    (x y : LatticeVertex) :
    φ.toMeasure.real (infiniteAt x) * φ.toMeasure.real (infiniteAt y) ≤
      φ.toMeasure.real (infiniteAt x ∩ infiniteAt y) := by
  let A : ℕ → Set LatticeConfiguration := wiredEscapeApprox x
  let B : ℕ → Set LatticeConfiguration := wiredEscapeApprox y
  let C : ℕ → Set LatticeConfiguration := fun n => A n ∩ B n
  have hAanti : Antitone A := wiredEscapeApprox_antitone x
  have hBanti : Antitone B := wiredEscapeApprox_antitone y
  have hCanti : Antitone C := by
    intro m n hmn ω hω
    exact ⟨hAanti hmn hω.1, hBanti hmn hω.2⟩
  have hAmeas (n : ℕ) : MeasurableSet (A n) := wiredEscapeApprox_measurable x n
  have hBmeas (n : ℕ) : MeasurableSet (B n) := wiredEscapeApprox_measurable y n
  have hCmeas (n : ℕ) : MeasurableSet (C n) := (hAmeas n).inter (hBmeas n)
  have hAseq : Tendsto (fun n => φ.toMeasure.real (A n)) atTop
      (𝓝 (φ.toMeasure.real (⋂ n, A n))) :=
    decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := A)
      hAanti hAmeas (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  have hBseq : Tendsto (fun n => φ.toMeasure.real (B n)) atTop
      (𝓝 (φ.toMeasure.real (⋂ n, B n))) :=
    decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := B)
      hBanti hBmeas (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  have hCseq : Tendsto (fun n => φ.toMeasure.real (C n)) atTop
      (𝓝 (φ.toMeasure.real (⋂ n, C n))) :=
    decreasing_event_diagonal_tendsto (μs := fun _ : ℕ => φ) (μ := φ) (E := C)
      hCanti hCmeas (fun _ => tendsto_const_nhds) (fun _ => le_rfl)
  have hIA : (⋂ n, A n) = infiniteAt x := by
    simpa only [A] using wiredEscapeApprox_iInter x
  have hIB : (⋂ n, B n) = infiniteAt y := by
    simpa only [B] using wiredEscapeApprox_iInter y
  have hIC : (⋂ n, C n) = infiniteAt x ∩ infiniteAt y := by
    calc
      (⋂ n, C n) = (⋂ n, A n) ∩ (⋂ n, B n) := by
        ext ω
        simp only [C, Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro h
          exact ⟨fun n => (h n).1, fun n => (h n).2⟩
        · rintro ⟨hA, hB⟩ n
          exact ⟨hA n, hB n⟩
      _ = infiniteAt x ∩ infiniteAt y := by rw [hIA, hIB]
  have hAseq' : Tendsto (fun n => φ.toMeasure.real (A n)) atTop
      (𝓝 (φ.toMeasure.real (infiniteAt x))) := by
    simpa only [hIA] using hAseq
  have hBseq' : Tendsto (fun n => φ.toMeasure.real (B n)) atTop
      (𝓝 (φ.toMeasure.real (infiniteAt y))) := by
    simpa only [hIB] using hBseq
  have hCseq' : Tendsto (fun n => φ.toMeasure.real (C n)) atTop
      (𝓝 (φ.toMeasure.real (infiniteAt x ∩ infiniteAt y))) := by
    simpa only [hIC] using hCseq
  have hprod := hAseq'.mul hBseq'
  have hfinite (n : ℕ) : φ.toMeasure.real (A n) * φ.toMeasure.real (B n) ≤
      φ.toMeasure.real (C n) := by
    exact wired_clopen_positive_association θ φ hφ (A n) (B n)
      (wiredDataEvent_isClopen n _) (wiredDataEvent_isClopen n _)
      (wiredEscapeApprox_upper x n) (wiredEscapeApprox_upper y n)
  exact le_of_tendsto_of_tendsto' hprod hCseq' hfinite

end
end PottsDiscontinuity.PottsThm
