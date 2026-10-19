module

public import PottsDiscontinuity.Potts.LocalFreeConnections
public import PottsDiscontinuity.Potts.WiredConnectionEvents

/-! Increasing finite-path events for free connection data. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

/-- The finite free partition, with isolated exterior vertices retained. -/
def freeDataFiniteEvent (n : ℕ) (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  {C | ∀ z ∈ F, z.1 = z.2 ∨ ∃ (hx : z.1 ∈ box n) (hy : z.2 ∈ box n),
      (FK.openGraph _ C).Reachable ⟨z.1, hx⟩ ⟨z.2, hy⟩}

def freeDataEvent (n : ℕ) (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) : Set FK.LatticeConfiguration :=
  {ω | ∀ z ∈ F, (localFreeGraph (rcInfiniteOpenGraph ω) n).Reachable z.1 z.2}

def infiniteFreeDataEvent (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) : Set FK.LatticeConfiguration :=
  {ω | ∀ z ∈ F, (rcInfiniteOpenGraph ω).Reachable z.1 z.2}

private theorem localFreeGraph_eq_map (n : ℕ) (ω : FK.LatticeConfiguration) :
    localFreeGraph (rcInfiniteOpenGraph ω) n =
      (FK.openGraph _ (boxObservation n ω)).map (show ↥(box n : Set (ℤ × ℤ)) ↪ (ℤ × ℤ) from
        ⟨Subtype.val, Subtype.val_injective⟩) := by
  ext x y
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨hxy, hx, hy⟩
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_, rfl, rfl⟩
    unfold boxObservation
    rw [openGraph_bool_adj_iff]
    obtain ⟨h, he⟩ := (infiniteOpenGraph_adj_iff ω x y).mp hxy
    exact ⟨h, he⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    refine ⟨?_, a.property, b.property⟩
    unfold boxObservation at hab
    rw [openGraph_bool_adj_iff] at hab
    obtain ⟨h, he⟩ := hab
    exact (infiniteOpenGraph_adj_iff ω a.val b.val).mpr ⟨h, he⟩

theorem freeDataEvent_eq_observation (n : ℕ) (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    freeDataEvent n F = boxObservationEvent n (freeDataFiniteEvent n F) := by
  ext ω
  change (∀ z ∈ F, (localFreeGraph (rcInfiniteOpenGraph ω) n).Reachable z.1 z.2) ↔ _
  rw [localFreeGraph_eq_map]
  constructor
  · intro h z hz
    rcases z with ⟨x, y⟩
    rcases (FK.reachable_isolatedExtension _ _ _ _).mp (h (x, y) hz) with heq | ⟨a, b, hab, ha, hb⟩
    · exact Or.inl heq
    · change a.val = x at ha
      change b.val = y at hb
      subst x y
      exact Or.inr ⟨a.property, b.property, hab⟩
  · intro h z hz
    apply (FK.reachable_isolatedExtension _ _ _ _).mpr
    rcases h z hz with heq | ⟨hx, hy, hxy⟩
    · exact Or.inl heq
    · exact Or.inr ⟨⟨z.1, hx⟩, ⟨z.2, hy⟩, hxy, rfl, rfl⟩

theorem freeDataEvent_isClopen (n : ℕ) (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    IsClopen (freeDataEvent n F) := by
  rw [freeDataEvent_eq_observation]
  exact boxObservationEvent_isClopen _ _

theorem freeDataEvent_monotone (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    Monotone (fun n => freeDataEvent n F) := by
  intro m n hmn ω hω z hz
  exact localFreeGraph_reachable_mono _ _ _ hmn (hω z hz)

theorem iUnion_freeDataEvent (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    (⋃ n, freeDataEvent n F) = infiniteFreeDataEvent F := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    intro z hz
    exact (hn z hz).mono (localFreeGraph_le _ n)
  · intro h
    obtain ⟨n, hn⟩ := (finite_free_connections_eventually (rcInfiniteOpenGraph ω) F).exists
    exact Set.mem_iUnion.mpr ⟨n, fun z hz => (hn z hz).mpr (h z hz)⟩

theorem freeDataFiniteEvent_upper (n : ℕ) (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    IsUpperSet (freeDataFiniteEvent n F) := by
  intro C D hCD hC z hz
  rcases hC z hz with heq | ⟨hx, hy, hxy⟩
  · exact Or.inl heq
  · exact Or.inr ⟨hx, hy, FK.actualConnected_mono hCD hxy⟩

theorem localFreeGraph_reachable_inside (n : ℕ) (ω : FK.LatticeConfiguration)
    (x y : ↥(box n : Set (ℤ × ℤ))) :
    (localFreeGraph (rcInfiniteOpenGraph ω) n).Reachable x.val y.val ↔
      (FK.openGraph _ (boxObservation n ω)).Reachable x y := by
  rw [localFreeGraph_eq_map]
  exact FK.reachable_isolatedExtension_apply _ ⟨Subtype.val, Subtype.val_injective⟩ x y

end
end PottsDiscontinuity.Potts
