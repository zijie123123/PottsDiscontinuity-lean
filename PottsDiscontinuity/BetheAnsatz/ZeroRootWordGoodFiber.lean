module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordPartition

/-!
# Root-incident fibers as the canonical T₁ index

The condition that every ML edge of a nonconstant word touches the root slot
is exactly the good fiber represented by one root-incident term index.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Raw data for a permutation, word, and root slot. -/
abbrev RootFiberRawData (n : ℕ) :=
  Fin (n + 1) × (Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool))

/-- A nonconstant word fiber for which every ML edge touches the root slot. -/
def RootIncidentFiberPredicate {n : ℕ} (l : Fin (n + 1))
    (d : RootFiberRawData n) : Prop :=
  d.2.1 d.1 = l ∧
    d.2.2 ≠ (fun _ => true) ∧ d.2.2 ≠ (fun _ => false) ∧
      ∀ a, d.2.2 a = false → d.2.2 (finRotate (n + 1) a) = true →
        d.1 = a ∨ d.1 = finRotate (n + 1) a

/-- Root-slot data satisfying the unique-root-incident ML condition. -/
abbrev RootIncidentFiberTermIndex (n : ℕ) (l : Fin (n + 1)) :=
  {d : RootFiberRawData n // RootIncidentFiberPredicate l d}

/-- Forget the marked edge and endpoint side of a root-incident index. -/
noncomputable def rootIncidentFiberUnderlying {n : ℕ} {l : Fin (n + 1)}
    (i : RootIncidentTermIndex n l) : RootIncidentFiberTermIndex n l := by
  let r := if i.side then t1EdgeLeft i.edge else t1EdgeRight i.edge
  have htrue : i.w ≠ fun _ => true := by
    intro h
    have := congrFun h (t1EdgeLeft i.edge)
    rw [i.hleft] at this
    cases this
  have hfalse : i.w ≠ fun _ => false := by
    intro h
    have := congrFun h (t1EdgeRight i.edge)
    rw [i.hright] at this
    cases this
  have hAll : ∀ a, i.w a = false → i.w (finRotate (n + 1) a) = true →
      r = a ∨ r = finRotate (n + 1) a := by
    intro a ha hb
    have hEdge := i.hunique a ha hb
    cases hs : i.side
    · right
      calc
        r = t1EdgeRight i.edge := by simp [r, hs]
        _ = finRotate (n + 1) (t1EdgeLeft i.edge) :=
          (t1EdgeLeft_rotate i.edge).symm
        _ = finRotate (n + 1) a := by rw [← hEdge]
    · left
      calc
        r = t1EdgeLeft i.edge := by simp [r, hs]
        _ = a := hEdge.symm
  exact ⟨(r, (i.σ.1, i.w)), ⟨i.σ.2, htrue, hfalse, hAll⟩⟩

/-- The forgotten raw data are injective on root-incident indices. -/
theorem rootIncidentFiberUnderlying_injective {n : ℕ} {l : Fin (n + 1)}
    (hn : 0 < n) :
    Function.Injective (rootIncidentFiberUnderlying (n := n) (l := l)) := by
  intro i j hij
  apply rootIncidentUnderlying_injective hn
  have hraw := congrArg Subtype.val hij
  apply Prod.ext
  · exact congrArg (fun d : RootFiberRawData n => d.2.1) hraw
  · exact congrArg (fun d : RootFiberRawData n => d.2.2) hraw

/-- Every good root-slot fiber determines its unique marked ML edge and its
root endpoint orientation. -/
theorem rootIncidentFiberUnderlying_surjective {n : ℕ} {l : Fin (n + 1)} :
    Function.Surjective (rootIncidentFiberUnderlying (n := n) (l := l)) := by
  intro q
  rcases q with ⟨⟨r, σ, w⟩, ⟨hσ, hL, hM, hAll⟩⟩
  let σ' : RootSlotPerm l r := ⟨σ, hσ⟩
  obtain ⟨i, hiσ, hiw⟩ :=
    exists_rootIncidentTerm_of_allMLIncident r σ' w hL hM hAll
  have hslot : (if i.side then t1EdgeLeft i.edge else t1EdgeRight i.edge) = r := by
    apply σ.injective
    calc
      σ (if i.side then t1EdgeLeft i.edge else t1EdgeRight i.edge) = l := by
        simpa [hiσ] using i.σ.2
      _ = σ r := hσ.symm
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hslot
  · apply Prod.ext
    · exact hiσ
    · exact hiw

/-- Good nonconstant root-slot fibers are in bijection with the root-incident
T₁ term indices. -/
noncomputable def rootIncidentFiberEquiv {n : ℕ} {l : Fin (n + 1)}
    (hn : 0 < n) : RootIncidentTermIndex n l ≃ RootIncidentFiberTermIndex n l :=
  Equiv.ofBijective (rootIncidentFiberUnderlying (n := n) (l := l))
    ⟨rootIncidentFiberUnderlying_injective hn,
      rootIncidentFiberUnderlying_surjective⟩

end PottsDiscontinuity.BetheAnsatz
