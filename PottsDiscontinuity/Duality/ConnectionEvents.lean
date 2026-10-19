module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Duality.ScreenBridge
public import PottsDiscontinuity.FK.BoxCylinders
public import PottsDiscontinuity.FK.Wiring

/-! Finite actual-path witnesses for whole-plane connectivity. -/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.Duality

open FK FK.Medial

private lemma finite_openGraph_le (ω : LatticeConfiguration)
    (F : Finset squareLattice.edgeSet) (hF : ω ∈ LatticeConfiguration.allOpen F) :
    openGraph squareLattice F ≤ wholePlaneOpenPrimalGraph ω := by
  intro u v huv
  have hG := openGraph_le squareLattice F huv
  obtain ⟨e, he, heval⟩ := (openGraph_adj squareLattice F u v).1 huv
  have heq : e = ⟨s(u, v), squareLattice.mem_edgeSet.mpr hG⟩ := Subtype.ext heval
  refine ⟨hG, ?_⟩
  simpa only [← heq] using hF e he

/-- Every actual whole-plane connection is witnessed by finitely many open
original lattice edges, and conversely. -/
theorem mem_connectionEvent_iff_finite_witness
    (ω : LatticeConfiguration) (u v : LatticeVertex) :
    ω ∈ connectionEvent u v ↔ ∃ F : Finset squareLattice.edgeSet,
      ActualConnected squareLattice F u v ∧ ω ∈ LatticeConfiguration.allOpen F := by
  change (rcInfiniteOpenGraph ω).Reachable u v ↔ _
  rw [← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph]
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact ⟨∅, SimpleGraph.Reachable.refl _, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
    | @cons a b c hab p ih =>
      obtain ⟨F, hconn, hF⟩ := ih
      obtain ⟨hG, hopen⟩ := hab
      let e : squareLattice.edgeSet := ⟨s(a, b), squareLattice.mem_edgeSet.mpr hG⟩
      have hadj : (openGraph squareLattice (insert e F)).Adj a b := by
        rw [openGraph_adj]
        exact ⟨e, Finset.mem_insert_self _ _, rfl⟩
      refine ⟨insert e F, hadj.reachable.trans
        (actualConnected_mono (Finset.subset_insert _ _) hconn), ?_⟩
      intro d hd
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact hopen
      · exact hF d hd
  · rintro ⟨F, hconn, hF⟩
    exact hconn.mono (finite_openGraph_le ω F hF)

/-- A finite original-edge configuration connecting the prescribed vertices. -/
abbrev ConnectionWitness (u v : LatticeVertex) :=
  {F : Finset squareLattice.edgeSet // ActualConnected squareLattice F u v}

/-- A finite union of finite path cylinders. -/
def finiteConnectionUnion (u v : LatticeVertex) (S : Finset (ConnectionWitness u v)) :
    Set LatticeConfiguration :=
  ⋃ F ∈ S, LatticeConfiguration.allOpen F.val

lemma finiteConnectionUnion_isClopen (u v : LatticeVertex)
    (S : Finset (ConnectionWitness u v)) : IsClopen (finiteConnectionUnion u v S) :=
  isClopen_biUnion_finset (fun F _ => LatticeConfiguration.allOpen_isClopen F.val)

lemma allOpen_isUpperSet (F : Finset squareLattice.edgeSet) :
    IsUpperSet (LatticeConfiguration.allOpen F) := by
  intro ω η hle hω e he
  have h := hle e
  rw [hω e he] at h
  cases hη : η e
  · rw [hη] at h
    exact Bool.le_iff_imp.1 h rfl
  · rfl

lemma finiteConnectionUnion_isUpperSet (u v : LatticeVertex)
    (S : Finset (ConnectionWitness u v)) : IsUpperSet (finiteConnectionUnion u v S) := by
  intro ω η hle hω
  obtain ⟨F, hF, hω⟩ := Set.mem_iUnion₂.1 hω
  exact Set.mem_iUnion₂.2 ⟨F, hF, allOpen_isUpperSet F.val hle hω⟩

lemma finiteConnectionUnion_mono (u v : LatticeVertex) :
    Monotone (finiteConnectionUnion u v) := by
  intro S T hST ω hω
  obtain ⟨F, hF, hω⟩ := Set.mem_iUnion₂.1 hω
  exact Set.mem_iUnion₂.2 ⟨F, hST hF, hω⟩

lemma connectionEvent_eq_iUnion (u v : LatticeVertex) :
    connectionEvent u v = ⋃ S : Finset (ConnectionWitness u v), finiteConnectionUnion u v S := by
  classical
  ext ω
  rw [mem_connectionEvent_iff_finite_witness]
  constructor
  · rintro ⟨F, hconn, hF⟩
    exact Set.mem_iUnion.2 ⟨{⟨F, hconn⟩},
      Set.mem_iUnion₂.2 ⟨⟨F, hconn⟩, Finset.mem_singleton_self _, hF⟩⟩
  · intro h
    obtain ⟨S, hS⟩ := Set.mem_iUnion.1 h
    obtain ⟨F, _, hF⟩ := Set.mem_iUnion₂.1 hS
    exact ⟨F.val, F.property, hF⟩

lemma connectionEvent_isOpen (u v : LatticeVertex) : IsOpen (connectionEvent u v) := by
  rw [connectionEvent_eq_iUnion]
  exact isOpen_iUnion (fun S => (finiteConnectionUnion_isClopen u v S).isOpen)

lemma connectionEvent_measurableSet (u v : LatticeVertex) :
    MeasurableSet (connectionEvent u v) := (connectionEvent_isOpen u v).measurableSet

lemma measure_connectionEvent_eq_iSup (μ : Measure LatticeConfiguration) (u v : LatticeVertex) :
    μ (connectionEvent u v) =
      ⨆ S : Finset (ConnectionWitness u v), μ (finiteConnectionUnion u v S) := by
  rw [connectionEvent_eq_iUnion]
  exact (finiteConnectionUnion_mono u v).directed_le.measure_iUnion

end PottsDiscontinuity.Duality
