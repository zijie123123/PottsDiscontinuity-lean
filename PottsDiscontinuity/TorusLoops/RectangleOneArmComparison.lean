module

public import PottsDiscontinuity.CorrLength.ConnectionEvents
public import PottsDiscontinuity.Zhang.BoundaryLimit

/-!
# Free-box comparison for one-arm events

The free finite-box law is dominated by the canonical free limit on the
one-arm event. The event is approximated from below by finite-witness clopen
increasing events, so this comparison does not assume that the full one-arm
event itself is clopen.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.CorrLength
open PottsDiscontinuity.Zhang

noncomputable section

noncomputable def oneArmWitnessEnumeration :
    ℕ → LatticeVertex × Finset squareLattice.edgeSet :=
  (exists_surjective_nat (LatticeVertex × Finset squareLattice.edgeSet)).choose

private theorem oneArmWitnessEnumeration_surjective :
    Function.Surjective oneArmWitnessEnumeration :=
  (exists_surjective_nat (LatticeVertex × Finset squareLattice.edgeSet)).choose_spec

/-- Finite-witness approximations to connection from the origin to any vertex
at coordinate radius at least `k`. -/
def freeOneArmApprox (k n : ℕ) : Set LatticeConfiguration :=
  ⋃ i : {i : ℕ // i ≤ n},
    if k ≤ boxRadius (oneArmWitnessEnumeration i).1 then
      finiteConnectionEvent (0, 0) (oneArmWitnessEnumeration i).1
        (oneArmWitnessEnumeration i).2
    else ∅

private theorem finiteConnectionEvent_isClopen (u v : LatticeVertex)
    (F : Finset squareLattice.edgeSet) :
    IsClopen (finiteConnectionEvent u v F) := by
  by_cases hconn : ActualConnected squareLattice F u v
  · simpa [finiteConnectionEvent, hconn] using LatticeConfiguration.allOpen_isClopen F
  · simpa [finiteConnectionEvent, hconn] using
      (isClopen_empty : IsClopen (∅ : Set LatticeConfiguration))

theorem freeOneArmApprox_mono (k : ℕ) : Monotone (freeOneArmApprox k) := by
  intro n m hnm ω hω
  rcases Set.mem_iUnion.mp hω with ⟨i, hi⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨i.1, i.property.trans hnm⟩, ?_⟩
  simpa using hi

theorem freeOneArmApprox_isClopen (k n : ℕ) : IsClopen (freeOneArmApprox k n) := by
  unfold freeOneArmApprox
  apply isClopen_iUnion_of_finite
  intro i
  by_cases hk : k ≤ boxRadius (oneArmWitnessEnumeration i).1
  · simpa [freeOneArmApprox, hk] using
      (finiteConnectionEvent_isClopen (0, 0) (oneArmWitnessEnumeration i).1
        (oneArmWitnessEnumeration i).2)
  · simpa [hk] using (isClopen_empty : IsClopen (∅ : Set LatticeConfiguration))

theorem freeOneArmApprox_isUpperSet (k n : ℕ) : IsUpperSet (freeOneArmApprox k n) := by
  intro ω η hωη hω
  rcases Set.mem_iUnion.mp hω with ⟨i, hi⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  by_cases hk : k ≤ boxRadius (oneArmWitnessEnumeration i).1
  · have hη := finiteConnectionEvent_isUpperSet (0, 0)
      (oneArmWitnessEnumeration i).1 (oneArmWitnessEnumeration i).2 hωη
      (by simpa [hk] using hi)
    simpa [hk] using hη
  · simp [hk] at hi

theorem iUnion_freeOneArmApprox (k : ℕ) :
    (⋃ n, freeOneArmApprox k n) = oneArmEvent k := by
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
    rcases Set.mem_iUnion.mp hn with ⟨i, hi⟩
    have hk : k ≤ boxRadius (oneArmWitnessEnumeration i).1 := by
      by_contra h
      simp [h] at hi
    have hconn : ω ∈ finiteConnectionEvent (0, 0)
        (oneArmWitnessEnumeration i).1 (oneArmWitnessEnumeration i).2 := by
      simpa [hk] using hi
    refine ⟨(oneArmWitnessEnumeration i).1, hk, ?_⟩
    exact (connectionEvent_iff_rcInfiniteReachable (0, 0)
      (oneArmWitnessEnumeration i).1 ω).mp
        ⟨(oneArmWitnessEnumeration i).2, hconn.1, hconn.2⟩
  · rintro ⟨y, hy, hreach⟩
    have hconn : ω ∈ connectionEvent (0, 0) y :=
      (connectionEvent_iff_rcInfiniteReachable (0, 0) y ω).mpr hreach
    rcases hconn with ⟨F, hFconn, hFopen⟩
    obtain ⟨i, hi⟩ := oneArmWitnessEnumeration_surjective (y, F)
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    unfold freeOneArmApprox
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, le_rfl⟩, ?_⟩
    have hk : k ≤ boxRadius (oneArmWitnessEnumeration i).1 := by
      simpa [hi] using hy
    have hfin : ω ∈ finiteConnectionEvent (0, 0)
        (oneArmWitnessEnumeration i).1 (oneArmWitnessEnumeration i).2 := by
      simpa [hi] using (show ω ∈ finiteConnectionEvent (0, 0) y F from
        ⟨hFconn, hFopen⟩)
    simp [hk, hfin]

end
end PottsDiscontinuity.TorusLoops
