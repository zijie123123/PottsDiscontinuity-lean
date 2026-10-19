module

public import PottsDiscontinuity.FK.Graph
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic

/-!
# Counting components after wiring a vertex boundary

The quotient definition of finite FK components agrees with the description
that counts every component disjoint from the boundary separately and all
components meeting the boundary as one. This proof is original to this port.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

open Classical

variable {V : Type*}

abbrev boundaryAvoidingComponents (H : SimpleGraph V) (W : Set V) :=
  {c : H.ConnectedComponent // ∀ x, H.connectedComponentMk x = c → x ∉ W}

def componentBoundaryLabel (H : SimpleGraph V) (W : Set V)
    (c : H.ConnectedComponent) : Option (boundaryAvoidingComponents H W) := by
  classical
  exact if h : ∀ y, H.connectedComponentMk y = c → y ∉ W
    then some ⟨c, h⟩ else none

def wiredComponentLabel (H : SimpleGraph V) (W : Set V) (x : V) :
    Option (boundaryAvoidingComponents H W) :=
  componentBoundaryLabel H W (H.connectedComponentMk x)

private theorem wiredComponentLabel_eq_of_connected (H : SimpleGraph V) (W : Set V)
    {x y : V} (hxy : H.Reachable x y) :
    wiredComponentLabel H W x = wiredComponentLabel H W y := by
  have hc : H.connectedComponentMk x = H.connectedComponentMk y :=
    SimpleGraph.ConnectedComponent.sound hxy
  exact congrArg (componentBoundaryLabel H W) hc

private theorem wiredComponentLabel_eq_none (H : SimpleGraph V) (W : Set V)
    {x : V} (hx : x ∈ W) : wiredComponentLabel H W x = none := by
  have hn : ¬ ∀ y, H.connectedComponentMk y = H.connectedComponentMk x → y ∉ W := by
    intro h
    exact h x rfl hx
  simp only [wiredComponentLabel, componentBoundaryLabel, dite_eq_right hn]

private theorem wiredComponentSetoid_eq_ker (H : SimpleGraph V) (W : Set V) :
    H.reachableSetoid ⊔ (BoundaryCondition.wired W).partition =
      Setoid.ker (wiredComponentLabel H W) := by
  classical
  apply le_antisymm
  · apply sup_le
    · intro x y hxy
      exact wiredComponentLabel_eq_of_connected H W hxy
    · intro x y hxy
      rcases (BoundaryCondition.wired_rel W x y).mp hxy with rfl | ⟨hx, hy⟩
      · rfl
      · exact (wiredComponentLabel_eq_none H W hx).trans
          (wiredComponentLabel_eq_none H W hy).symm
  · intro x y hxy
    change wiredComponentLabel H W x = wiredComponentLabel H W y at hxy
    by_cases hx : ∀ z, H.connectedComponentMk z = H.connectedComponentMk x → z ∉ W
    · by_cases hy : ∀ z, H.connectedComponentMk z = H.connectedComponentMk y → z ∉ W
      · simp only [wiredComponentLabel, componentBoundaryLabel, dite_eq_left hx,
          dite_eq_left hy, Option.some.injEq] at hxy
        have hc : H.connectedComponentMk x = H.connectedComponentMk y :=
          congrArg Subtype.val hxy
        exact (le_sup_left : H.reachableSetoid ≤
          H.reachableSetoid ⊔ (BoundaryCondition.wired W).partition)
            (SimpleGraph.ConnectedComponent.exact hc)
      · simp only [wiredComponentLabel, componentBoundaryLabel, dite_eq_left hx,
          dite_eq_right hy, Option.some_ne_none] at hxy
    · by_cases hy : ∀ z, H.connectedComponentMk z = H.connectedComponentMk y → z ∉ W
      · simp only [wiredComponentLabel, componentBoundaryLabel, dite_eq_right hx,
          dite_eq_left hy] at hxy
        cases hxy
      · push Not at hx hy
        obtain ⟨a, ha, haW⟩ := hx
        obtain ⟨b, hb, hbW⟩ := hy
        let s := H.reachableSetoid ⊔ (BoundaryCondition.wired W).partition
        have hxa : s.r x a := (le_sup_left : H.reachableSetoid ≤ s)
          (SimpleGraph.ConnectedComponent.exact ha.symm)
        have hab : s.r a b := (le_sup_right : (BoundaryCondition.wired W).partition ≤ s)
          ((BoundaryCondition.wired_rel W a b).mpr (Or.inr ⟨haW, hbW⟩))
        have hby : s.r b y := (le_sup_left : H.reachableSetoid ≤ s)
          (SimpleGraph.ConnectedComponent.exact hb)
        exact s.trans hxa (s.trans hab hby)

private theorem wiredComponentLabel_surjective (H : SimpleGraph V) (W : Set V)
    (hW : W.Nonempty) : Function.Surjective (wiredComponentLabel H W) := by
  classical
  intro c
  cases c with
  | none =>
      obtain ⟨x, hx⟩ := hW
      exact ⟨x, wiredComponentLabel_eq_none H W hx⟩
  | some c =>
      obtain ⟨x, hx⟩ := Quot.mk_surjective c.val
      have hc : ∀ y, H.connectedComponentMk y = H.connectedComponentMk x → y ∉ W := by
        intro y hy
        exact c.property y (hy.trans hx)
      refine ⟨x, ?_⟩
      simp only [wiredComponentLabel, componentBoundaryLabel, dite_eq_left hc]
      congr 1
      exact Subtype.ext hx

/-- Wiring a nonempty boundary leaves one boundary component and every original
component disjoint from that boundary. -/
theorem card_wiredComponentQuotient_of_nonempty [Finite V]
    (H : SimpleGraph V) (W : Set V) (hW : W.Nonempty) :
    Nat.card (Quotient (H.reachableSetoid ⊔ (BoundaryCondition.wired W).partition)) =
      Nat.card {c : H.ConnectedComponent //
        ∀ x, H.connectedComponentMk x = c → x ∉ W} + 1 := by
  classical
  rw [wiredComponentSetoid_eq_ker]
  have hcard := Nat.card_congr
    (Setoid.quotientKerEquivOfSurjective (wiredComponentLabel H W)
      (wiredComponentLabel_surjective H W hW))
  let : Fintype (boundaryAvoidingComponents H W) := Fintype.ofFinite _
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_option]
  rw [Nat.card_eq_fintype_card]

/-- The ported wired component count equals the frozen description: components
avoiding the boundary plus one exactly when a component meets the boundary. -/
theorem componentCount_wired_eq_boundary_avoiding [Finite V]
    (G : SimpleGraph V) (W : Set V) (A : Configuration G) :
    componentCount G (BoundaryCondition.wired W) A =
      Nat.card {c : (openGraph G A).ConnectedComponent //
        ∀ x, (openGraph G A).connectedComponentMk x = c → x ∉ W} +
      if ∃ c : (openGraph G A).ConnectedComponent,
          ∃ x, (openGraph G A).connectedComponentMk x = c ∧ x ∈ W then 1 else 0 := by
  classical
  have hex : (∃ c : (openGraph G A).ConnectedComponent,
      ∃ x, (openGraph G A).connectedComponentMk x = c ∧ x ∈ W) ↔ W.Nonempty := by
    constructor
    · rintro ⟨c, x, _, hx⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨(openGraph G A).connectedComponentMk x, x, rfl, hx⟩
  rw [hex]
  by_cases hW : W.Nonempty
  · rw [ite_eq_left hW]
    exact card_wiredComponentQuotient_of_nonempty (openGraph G A) W hW
  · have hWe : W = ∅ := Set.not_nonempty_iff_eq_empty.mp hW
    subst W
    have hp : (BoundaryCondition.wired (∅ : Set V)).partition = ⊥ := by
      apply Setoid.ext
      intro x y
      change (x = y ∨ x ∈ (∅ : Set V) ∧ y ∈ (∅ : Set V)) ↔ x = y
      simp
    simp only [componentCount, componentSetoid, hp, sup_bot_eq,
      Set.mem_empty_iff_false, not_false_eq_true, implies_true, Nat.card_subtype_true,
      Set.not_nonempty_empty, ite_false, add_zero]
    rfl

end
end PottsDiscontinuity.FK
