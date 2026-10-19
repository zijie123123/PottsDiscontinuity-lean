module

public import PottsDiscontinuity.Duality.ScreenBridge
public import PottsDiscontinuity.Potts.BoxObservation
public import PottsDiscontinuity.Potts.LocalWiredConnections

/-! Increasing clopen events encoding finite wired connection data. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

local instance eventBoundaryFintype (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _

/-- The frozen infinite open graph retains exactly the sampled lattice bonds. -/
theorem infiniteOpenGraph_adj_iff (ω : FK.LatticeConfiguration) (x y : ℤ × ℤ) :
    (rcInfiniteOpenGraph ω).Adj x y ↔
      ∃ h : squareLattice.Adj x y, ω ⟨s(x, y), squareLattice.mem_edgeSet.mpr h⟩ = true := by
  rw [rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨h, hω⟩, _⟩
    exact ⟨squareLattice.mem_edgeSet.mp h, hω⟩
  · rintro ⟨h, hω⟩
    exact ⟨⟨squareLattice.mem_edgeSet.mpr h, hω⟩, h.ne⟩

theorem infiniteOpenGraph_le (ω : FK.LatticeConfiguration) : rcInfiniteOpenGraph ω ≤ squareLattice := by
  intro x y hxy
  exact ((infiniteOpenGraph_adj_iff ω x y).mp hxy).choose

/-- Wire the boundary of a sampled finite edge configuration to the ghost. -/
def wiredObservationGraph (n : ℕ)
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    SimpleGraph (Option ↥(box n : Set (ℤ × ℤ))) :=
  { Adj := fun a b => match a, b with
      | none, none => False
      | some x, some y => (FK.openGraph _ C).Adj x y
      | some x, none => x.val ∈ vertexBoundary (box n)
      | none, some y => y.val ∈ vertexBoundary (box n)
    symm := by
      constructor
      intro a b h
      cases a <;> cases b
      · exact h
      · exact h
      · exact h
      · exact h.symm
    loopless := by
      constructor
      intro a h
      cases a
      · exact h
      · exact SimpleGraph.irrefl _ h }

theorem wiredObservationGraph_eq (n : ℕ) (ω : FK.LatticeConfiguration) :
    wiredObservationGraph n (boxObservation n ω) = finiteWiredConnectionGraph (rcInfiniteOpenGraph ω) n := by
  ext a b
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => simp [wiredObservationGraph, finiteWiredConnectionGraph]
  | some x =>
    cases b with
    | none => simp [wiredObservationGraph, finiteWiredConnectionGraph]
    | some y =>
      change (FK.openGraph _ (boxObservation n ω)).Adj x y ↔ (rcInfiniteOpenGraph ω).Adj x.val y.val
      unfold boxObservation
      rw [openGraph_bool_adj_iff, infiniteOpenGraph_adj_iff]
      constructor
      · rintro ⟨h, he⟩
        exact ⟨h, he⟩
      · rintro ⟨h, he⟩
        exact ⟨h, he⟩

/-- The finite FK event asserting the indicated connections, including marks. -/
def wiredDataFiniteEvent (n : ℕ) (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  {C | ∀ z ∈ F, (wiredObservationGraph n C).Reachable
    (boxGhostProjection n z.1) (boxGhostProjection n z.2)}

/-- Positive moments of the finite wired connection partition. -/
def wiredDataEvent (n : ℕ) (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    Set FK.LatticeConfiguration :=
  {ω | ∀ z ∈ F, localWiredSetoid (rcInfiniteOpenGraph ω) n z.1 z.2}

/-- Positive moments of the partition with every infinite cluster merged. -/
def infiniteMergedDataEvent (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    Set FK.LatticeConfiguration :=
  {ω | ∀ z ∈ F, infiniteMergedSetoid (rcInfiniteOpenGraph ω) z.1 z.2}

theorem wiredDataEvent_eq_observation (n : ℕ)
    (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    wiredDataEvent n F = boxObservationEvent n (wiredDataFiniteEvent n F) := by
  ext ω
  change (∀ z ∈ F, localWiredSetoid (rcInfiniteOpenGraph ω) n z.1 z.2) ↔
    ∀ z ∈ F, (wiredObservationGraph n (boxObservation n ω)).Reachable
      (boxGhostProjection n z.1) (boxGhostProjection n z.2)
  rw [wiredObservationGraph_eq]
  rfl

theorem wiredDataEvent_isClopen (n : ℕ)
    (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) : IsClopen (wiredDataEvent n F) := by
  rw [wiredDataEvent_eq_observation]
  exact boxObservationEvent_isClopen _ _

theorem wiredDataEvent_antitone (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    Antitone (fun n => wiredDataEvent n F) := by
  intro m n hmn ω hω z hz
  exact localWiredSetoid_antitone _ (infiniteOpenGraph_le ω) hmn (hω z hz)

theorem iInter_wiredDataEvent (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    (⋂ n, wiredDataEvent n F) = infiniteMergedDataEvent F := by
  ext ω
  simp only [Set.mem_iInter, wiredDataEvent, infiniteMergedDataEvent, Set.mem_ofPred_eq]
  constructor
  · intro h z hz
    exact (localWiredSetoid_limit _ (infiniteOpenGraph_le ω) _ _).mp (fun n => h n z hz)
  · intro h n z hz
    exact (localWiredSetoid_limit _ (infiniteOpenGraph_le ω) _ _).mpr (h z hz) n

theorem wiredDataFiniteEvent_upper (n : ℕ)
    (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) : IsUpperSet (wiredDataFiniteEvent n F) := by
  intro C D hCD hC z hz
  have hg : wiredObservationGraph n C ≤ wiredObservationGraph n D := by
    intro a b hab
    cases a <;> cases b
    · exact hab.elim
    · exact hab
    · exact hab
    · change (FK.openGraph _ C).Adj _ _ at hab
      change (FK.openGraph _ D).Adj _ _
      rw [FK.openGraph_adj] at hab ⊢
      obtain ⟨e, he, heq⟩ := hab
      exact ⟨e, hCD he, heq⟩
  exact (hC z hz).mono hg

end
end PottsDiscontinuity.Potts
