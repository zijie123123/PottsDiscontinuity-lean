/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.LatticePorts
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.FK
open Medial
open Medial.LatticeAxis

 def cellBoundaryBonds (c : LatticeVertex) : Finset LatticeBond :=
  {⟨c, horizontal⟩, ⟨(c.1, c.2 + 1), horizontal⟩,
   ⟨c, vertical⟩, ⟨(c.1 + 1, c.2), vertical⟩}

theorem mem_cellBoundaryBonds_faceBase (c : LatticeVertex) (e : LatticeBond) :
    e ∈ cellBoundaryBonds c ↔ e.faceBase false = c ∨ e.faceBase true = c := by
  rcases c with ⟨x,y⟩
  rcases e with ⟨⟨a,b⟩, ax⟩
  cases ax <;> simp [cellBoundaryBonds, LatticeBond.faceBase] <;> omega

/-- Actual primal bonds separating a selected finite set of unit faces from its complement. -/
def latticeCellBoundaryBonds (S : Finset LatticeVertex) : Finset LatticeBond := by
  classical
  exact (S.biUnion cellBoundaryBonds).filter
    (fun e => (e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S))

theorem mem_latticeCellBoundaryBonds (S : Finset LatticeVertex) (e : LatticeBond) :
    e ∈ latticeCellBoundaryBonds S ↔
      ((e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S)) := by
  classical
  simp only [latticeCellBoundaryBonds, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_biUnion]
    by_cases ht : e.faceBase true ∈ S
    · exact ⟨e.faceBase true, ht,
        (mem_cellBoundaryBonds_faceBase _ _).2 (Or.inr rfl)⟩
    · have hf : e.faceBase false ∈ S := by
        by_contra hf
        exact h (by simp [ht, hf])
      exact ⟨e.faceBase false, hf,
        (mem_cellBoundaryBonds_faceBase _ _).2 (Or.inl rfl)⟩

theorem latticeCellBoundaryBonds_finite (S : Finset LatticeVertex) :
    (latticeCellBoundaryBonds S : Set LatticeBond).Finite := by
  exact Finset.finite_toSet _

/-- The graph whose edges are precisely the actual bonds crossing the face boundary. -/
def latticeCellBoundaryGraph (S : Finset LatticeVertex) : SimpleGraph LatticeVertex where
  Adj u v := squareLattice.Adj u v ∧ ∃ e ∈ latticeCellBoundaryBonds S, e.toSym2 = s(u,v)
  symm := ⟨by
    intro u v h
    rcases h with ⟨hadj, e, he, hsym⟩
    exact ⟨hadj.symm, e, he, hsym.trans Sym2.eq_swap⟩⟩
  loopless := ⟨by
    intro u h
    exact squareLattice.loopless.irrefl u h.1⟩

theorem latticeCellBoundaryGraph_le (S : Finset LatticeVertex) :
    latticeCellBoundaryGraph S ≤ squareLattice := by
  intro u v h
  exact h.1

theorem latticeCellBoundaryGraph_adj_iff (S : Finset LatticeVertex) (u v : LatticeVertex) :
    (latticeCellBoundaryGraph S).Adj u v ↔
      squareLattice.Adj u v ∧ ∃ e : LatticeBond,
        e.toSym2 = s(u,v) ∧
        ((e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S)) := by
  constructor
  · rintro ⟨hadj, e, he, hedge⟩
    exact ⟨hadj, e, hedge, (mem_latticeCellBoundaryBonds S e).mp he⟩
  · rintro ⟨hadj, e, hedge, hfaces⟩
    exact ⟨hadj, e, (mem_latticeCellBoundaryBonds S e).mpr hfaces, hedge⟩

end PottsDiscontinuity.FK
