module

public import PottsDiscontinuity.Potts.GhostConnectionLaw
public import PottsDiscontinuity.Potts.FinitePartitionLimits

/-! Exact expectations of marked partitions under the literal ghost representation. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace
local instance partitionBoundaryFintype (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _
local instance partitionShellFintype (n : ℕ) : Fintype (OuterShellEdge n) := Fintype.ofFinite _
local instance partitionSetoidFintype {A : Type*} [Finite A] : Fintype (Setoid A) := Fintype.ofFinite _

/-- The exact conditioned law transports every function of a finite marked
partition to the literal ghost law. -/
theorem conditionedOuterLaw_partitionExpectation {A : Type*} [Fintype A]
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (n : ℕ) (hn : 0 < n)
    (r : FK.Configuration (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))) → Setoid A)
    (g : (LiteralBond (box n) → Bool) → Setoid A) (K : Setoid A → ℝ)
    (hrg : ∀ ω η, r (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) = g ω) :
    partitionExpectation (conditionedOuterLaw (fkParameters q hq β hβ) n).toMeasure r K =
      ∑ ω, ghostRCProbability q (box n) β ω * K (g ω) := by
  unfold partitionExpectation
  have hprob (R : Setoid A) := conditionedOuterLaw_event_eq_ghost q hq β hβ n hn
    {C | r C = R} {ω | g ω = R} (fun ω η => by
      change r (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) = R ↔ g ω = R
      rw [hrg ω η])
  simp_rw [hprob, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr
  · ext ω; simp
  · intro ω _
    rw [Finset.sum_eq_single (g ω)]
    · simp
    · intro R _ hR
      simp [Ne.symm hR]
    · simp

end
end PottsDiscontinuity.Potts
