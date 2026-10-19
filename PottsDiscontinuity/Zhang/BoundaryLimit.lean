module

public import PottsDiscontinuity.RCInfinite.ClusterEvents

/-!
# One-arm limits

The coordinate-box one-arm probabilities converge to the probability that the
actual origin cluster is infinite. This is the continuity-from-above part of
Zhang's theorem, not the critical nonpercolation theorem itself.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.Zhang
open FK RCInfinite

/-- The coordinate radius defining the closed square boxes. -/
def boxRadius (x : LatticeVertex) : ℕ := max x.1.natAbs x.2.natAbs

lemma boxRadius_le_iff (x : LatticeVertex) (n : ℕ) :
    boxRadius x ≤ n ↔ x ∈ latticeBox (0, 0) n := by
  simp only [boxRadius, mem_latticeBox, zero_sub, zero_add]
  omega

lemma boxRadius_zero : boxRadius (0, 0) = 0 := rfl

lemma boxRadius_step {x y : LatticeVertex} (h : squareLattice.Adj x y) :
    boxRadius y ≤ boxRadius x + 1 := by
  rw [squareLattice_adj_iff] at h
  simp only [boxRadius]
  omega

/-- The origin connects to a vertex of coordinate radius at least `n`. -/
def oneArmEvent (n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ y, n ≤ boxRadius y ∧ (rcInfiniteOpenGraph ω).Reachable (0, 0) y}

/-- The origin connects to the inner boundary of the coordinate box of radius `n`.
At radius zero this is the certain event. -/
def boundaryConnectionEvent (n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ y, boxRadius y = n ∧ (rcInfiniteOpenGraph ω).Reachable (0, 0) y}

lemma oneArmEvent_antitone : Antitone oneArmEvent := by
  intro n m hnm ω hω
  obtain ⟨y, hy, hconn⟩ := hω
  exact ⟨y, hnm.trans hy, hconn⟩

lemma measurableSet_oneArmEvent (n : ℕ) : MeasurableSet (oneArmEvent n) := by
  have h := MeasurableSet.iUnion fun y : {y : LatticeVertex // n ≤ boxRadius y} =>
    measurableSet_open_reachable (0, 0) y.val
  convert h using 1
  ext ω
  simp only [oneArmEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop]

/-- A nearest-neighbor walk starting inside a radius and ending beyond it
visits the exact radius. -/
lemma walk_hits_radius {ω : LatticeConfiguration} {x y : LatticeVertex}
    (w : (rcInfiniteOpenGraph ω).Walk x y) (n : ℕ)
    (hx : boxRadius x ≤ n) (hy : n ≤ boxRadius y) :
    ∃ z, boxRadius z = n ∧ (rcInfiniteOpenGraph ω).Reachable x z := by
  induction w with
  | nil => exact ⟨_, Nat.le_antisymm hx hy, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hab w ih =>
    by_cases ha : boxRadius a = n
    · exact ⟨a, ha, SimpleGraph.Reachable.refl a⟩
    · obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω a b).mp hab
      have hstep : boxRadius b ≤ boxRadius a + 1 :=
        boxRadius_step (squareLattice.mem_edgeSet.mp he)
      have hb : boxRadius b ≤ n := by omega
      obtain ⟨z, hz, hbz⟩ := ih hb hy
      exact ⟨z, hz, hab.reachable.trans hbz⟩

lemma boundaryConnectionEvent_eq_oneArmEvent (n : ℕ) :
    boundaryConnectionEvent n = oneArmEvent n := by
  ext ω
  constructor
  · rintro ⟨y, hy, hconn⟩
    exact ⟨y, hy.ge, hconn⟩
  · rintro ⟨y, hy, ⟨w⟩⟩
    exact walk_hits_radius w n (by rw [boxRadius_zero]; exact Nat.zero_le _) hy

/-- Reaching arbitrarily large finite box boundaries is exactly infinitude of
the actual open cluster; no probability or uniqueness input is involved. -/
theorem iInter_oneArmEvent : (⋂ n, oneArmEvent n) = infiniteAt (0, 0) := by
  ext ω
  simp only [Set.mem_iInter]
  constructor
  · intro h
    apply (infinite_cluster_iff ω (0, 0)).mpr
    intro F
    obtain ⟨y, hy, hconn⟩ := h (F.sup boxRadius + 1)
    refine ⟨y, ?_, hconn⟩
    intro hyF
    have := Finset.le_sup (f := boxRadius) hyF
    omega
  · intro h n
    obtain ⟨y, hy, hconn⟩ := (infinite_cluster_iff ω (0, 0)).mp h
      (latticeBox (0, 0) n)
    exact ⟨y, (Nat.le_of_lt (Nat.lt_of_not_ge ((boxRadius_le_iff y n).not.mpr hy))), hconn⟩

/-- Continuity from above, for any finite measure on actual lattice configurations. -/
theorem tendsto_boundaryConnection_probability
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ] :
    Tendsto (fun n => μ (boundaryConnectionEvent n)) atTop
      (𝓝 (μ (infiniteAt (0, 0)))) := by
  simp_rw [boundaryConnectionEvent_eq_oneArmEvent]
  have h := tendsto_measure_iInter_atTop
    (μ := μ) (fun n => (measurableSet_oneArmEvent n).nullMeasurableSet)
    oneArmEvent_antitone ⟨0, measure_ne_top μ _⟩
  simpa only [Function.comp_def, iInter_oneArmEvent] using h

/-- The exact missing input for the zero boundary limit is origin
nonpercolation. This equivalence is not a proof of critical nonpercolation. -/
theorem tendsto_boundaryConnection_zero_iff
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ] :
    Tendsto (fun n => μ (boundaryConnectionEvent n)) atTop (𝓝 0) ↔
      μ (infiniteAt (0, 0)) = 0 := by
  constructor
  · intro h
    exact tendsto_nhds_unique (tendsto_boundaryConnection_probability μ) h
  · intro h
    simpa only [h] using tendsto_boundaryConnection_probability μ

end PottsDiscontinuity.Zhang
