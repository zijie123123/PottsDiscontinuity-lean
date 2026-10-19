/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.FK.Graph

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*}

/-- Boolean indicator of actual open connectivity to the seed set. This deliberately
uses `ActualConnected`, so boundary identifications play no role. -/
noncomputable def actualReachabilityLabel (G : SimpleGraph V) (A : Configuration G)
    (L : Finset V) (v : V) : Bool := by
  classical
  exact decide (∃ u, u ∈ L ∧ ActualConnected G A u v)

theorem actualReachabilityLabel_eq_true_iff (G : SimpleGraph V)
    (A : Configuration G) (L : Finset V) (v : V) :
    actualReachabilityLabel G A L v = true ↔
      ∃ u, u ∈ L ∧ ActualConnected G A u v := by
  classical
  simp [actualReachabilityLabel]

theorem actualReachabilityLabel_eq_true_of_mem (G : SimpleGraph V)
    (A : Configuration G) (L : Finset V) {v : V} (hv : v ∈ L) :
    actualReachabilityLabel G A L v = true := by
  apply (actualReachabilityLabel_eq_true_iff G A L v).2
  exact ⟨v, hv, SimpleGraph.Reachable.refl v⟩

theorem actualReachabilityLabel_eq_of_actualConnected (G : SimpleGraph V)
    (A : Configuration G) (L : Finset V) {x y : V}
    (hxy : ActualConnected G A x y) :
    actualReachabilityLabel G A L x = actualReachabilityLabel G A L y := by
  classical
  have hiff : (∃ u, u ∈ L ∧ ActualConnected G A u x) ↔
      (∃ u, u ∈ L ∧ ActualConnected G A u y) := by
    constructor
    · rintro ⟨u, hu, hux⟩
      exact ⟨u, hu, hux.trans hxy⟩
    · rintro ⟨u, hu, huy⟩
      exact ⟨u, hu, huy.trans hxy.symm⟩
  apply Bool.eq_iff_iff.mpr
  rw [actualReachabilityLabel_eq_true_iff, actualReachabilityLabel_eq_true_iff]
  exact hiff

theorem actualReachabilityLabel_eq_false_of_no_seed_path (G : SimpleGraph V)
    (A : Configuration G) (L R : Finset V)
    (hno : ∀ u, u ∈ L → ∀ v, v ∈ R → ¬ ActualConnected G A u v)
    {v : V} (hv : v ∈ R) :
    actualReachabilityLabel G A L v = false := by
  classical
  classical
  rw [actualReachabilityLabel]
  by_cases hp : ∃ u, u ∈ L ∧ ActualConnected G A u v
  · rcases hp with ⟨u, hu, huv⟩
    exact False.elim (hno u hu v hv huv)
  · simp [hp]

theorem actualEdge_mem_configuration_implies_labels_eq (G : SimpleGraph V)
    (A : Configuration G) (L : Finset V) {u v : V} (hG : s(u, v) ∈ G.edgeSet)
    (hA : (⟨s(u, v), hG⟩ : G.edgeSet) ∈ A) :
    actualReachabilityLabel G A L u = actualReachabilityLabel G A L v := by
  apply actualReachabilityLabel_eq_of_actualConnected G A L
  apply actualConnected_of_adj
  rw [openGraph_adj]
  exact ⟨⟨s(u, v), hG⟩, hA, rfl⟩

end PottsDiscontinuity.FK
