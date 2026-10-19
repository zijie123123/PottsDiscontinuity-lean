module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.ConditionalConnectionBound

/-! The exploration product bound, with the first crossing charged at most one. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK FK.FiniteProbability
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
open scoped Classical
local instance distinctProductEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance distinctProductEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The exact finite exploration product: each successive distinct connection
costs at most c, starting after the first explored cluster. -/
theorem distinctConnections_probability_le_pow (θ : Parameters) (x y : ℕ → V)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hcomp : ∀ j : ℕ, 1 ≤ j → ∀ A ∈ distinctConnections G x y j,
      ∀ (hx : x j ∈ actualMultiClusterComplementSet G (prefixSeeds x j) A)
        (hy : y j ∈ actualMultiClusterComplementSet G (prefixSeeds x j) A),
      (measure (G.induce (actualMultiClusterComplementSet G (prefixSeeds x j) A)) θ
        (BoundaryCondition.free ∅) (connectivityEvent _ ⟨x j,hx⟩ ⟨y j,hy⟩)).toReal ≤ c)
    (r : ℕ) (hr : 1 ≤ r) :
    (measure G θ (BoundaryCondition.free ∅) (distinctConnections G x y r)).toReal ≤ c^(r-1) := by
  rw [fk_measureReal_eq_expectation]
  induction r,hr using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self,pow_zero]
    calc
      _ ≤ expectation (law G θ (BoundaryCondition.free ∅)) (fun _ => 1) := by
        apply expectation_mono
        intro A
        by_cases ha : A ∈ distinctConnections G x y 1 <;> simp [ha]
      _ = 1 := expectation_const _ _
  | succ r hr ih =>
    rw [distinctConnections_succ]
    have hs := record_step_le (law G θ (BoundaryCondition.free ∅))
      (fkLaw_full_support G θ _) (clusterRecord G (prefixSeeds x r))
      (distinctConnections G x y r) (nextDistinctConnection G x y r)
      (fun A B h => distinctConnections_record_measurable G x y r A B h) c
      (fun A hA => nextDistinct_conditional_le G θ x y r A c hc0 (hcomp r hr A hA))
    refine hs.trans ?_
    calc
      _ ≤ c * c^(r-1) := mul_le_mul_of_nonneg_left ih hc0
      _ = c^((r+1)-1) := by
        rw [show (r+1)-1=(r-1)+1 by omega,pow_succ]
        ring

end
end PottsDiscontinuity.TorusExploration
