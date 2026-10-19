module

public import PottsDiscontinuity.FK.EndpointLimits
public import PottsDiscontinuity.Potts.NestedBoxComparison

/-! Actual free connection data is the increasing limit of finite open paths. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical Filter
noncomputable section

/-- Retain precisely the open edges whose endpoints belong to the box.
Exterior vertices remain isolated vertices of the common carrier. -/
def localFreeGraph (H : SimpleGraph (ℤ × ℤ)) (n : ℕ) : SimpleGraph (ℤ × ℤ) where
  Adj x y := H.Adj x y ∧ x ∈ box n ∧ y ∈ box n
  symm := by
    constructor
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy.symm, hy, hx⟩
  loopless := by
    constructor
    intro x h
    exact H.irrefl h.1

theorem localFreeGraph_le (H : SimpleGraph (ℤ × ℤ)) (n : ℕ) : localFreeGraph H n ≤ H :=
  fun _ _ h => h.1

theorem localFreeGraph_mono (H : SimpleGraph (ℤ × ℤ)) : Monotone (localFreeGraph H) := by
  intro m n hmn x y hxy
  exact ⟨hxy.1, box_mono hmn hxy.2.1, box_mono hmn hxy.2.2⟩

theorem localFreeGraph_reachable_mono (H : SimpleGraph (ℤ × ℤ)) (x y : ℤ × ℤ) :
    Monotone (fun n => (localFreeGraph H n).Reachable x y) := by
  intro m n hmn hxy
  exact hxy.mono (localFreeGraph_mono H hmn)

/-- Every actual open path is contained in a finite box. -/
theorem reachable_iff_exists_localFree (H : SimpleGraph (ℤ × ℤ)) (x y : ℤ × ℤ) :
    H.Reachable x y ↔ ∃ n, (localFreeGraph H n).Reachable x y := by
  constructor
  · rintro ⟨w⟩
    have he : ∀ᶠ n : ℕ in atTop, ∀ z ∈ w.support, z ∈ box n := by
      simpa only [List.mem_toFinset] using
        (eventually_all_finset w.support.toFinset).mpr (fun z _ => FK.eventually_mem_box z)
    obtain ⟨n, hn⟩ := he.exists
    let f : H.induce (box n : Set (ℤ × ℤ)) →g localFreeGraph H n :=
      { toFun := Subtype.val
        map_rel' := fun {a b} hab => ⟨hab, a.property, b.property⟩ }
    exact ⟨n, ⟨(w.induce (box n : Set (ℤ × ℤ)) hn).map f⟩⟩
  · rintro ⟨n, hxy⟩
    exact hxy.mono (localFreeGraph_le H n)

/-- On finitely many observed pairs, all actual connections eventually appear
simultaneously in the finite-box graph. -/
theorem finite_free_connections_eventually (H : SimpleGraph (ℤ × ℤ))
    (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ F,
      ((localFreeGraph H n).Reachable z.1 z.2 ↔ H.Reachable z.1 z.2) := by
  apply (eventually_all_finset F).mpr
  intro z _
  by_cases h : H.Reachable z.1 z.2
  · obtain ⟨m, hm⟩ := (reachable_iff_exists_localFree H z.1 z.2).mp h
    filter_upwards [eventually_ge_atTop m] with n hn
    exact ⟨fun _ => h, fun _ => localFreeGraph_reachable_mono H z.1 z.2 hn hm⟩
  · exact Filter.Eventually.of_forall (fun n =>
      ⟨fun hn => (h (hn.mono (localFreeGraph_le H n))).elim, fun hn => (h hn).elim⟩)

end
end PottsDiscontinuity.Potts
