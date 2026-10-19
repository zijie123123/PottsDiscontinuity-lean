module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.ClusterComplementFreeLaw
public import PottsDiscontinuity.TorusExploration.DistinctConnections
public import PottsDiscontinuity.TorusExploration.FiberAveraging
public import PottsDiscontinuity.TorusExploration.FiniteBoxComparison
public import PottsDiscontinuity.TorusExploration.InducedConnectivity

/-! A genuine conditional exploration bound after revealing complete clusters. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK FK.FiniteProbability
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
open scoped Classical
local instance conditionalConnectionEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance conditionalConnectionEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

lemma expectation_le_on_support {α : Type*} [Fintype α] (p : PMF α) (F H : α → ℝ)
    (h : ∀ a, a ∈ p.support → F a ≤ H a) : expectation p F ≤ expectation p H := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : p a=0
  · simp only [ha,ENNReal.toReal_zero,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg

lemma fkLaw_full_support (θ : Parameters) (ξ : BoundaryCondition V) (A : Configuration G) :
    A ∈ (law G θ ξ).support := by rw [law_support]; trivial

lemma clusterRecordConditional_eq (θ : Parameters) (S : Finset V) (A : Configuration G) :
    recordConditional (law G θ (BoundaryCondition.free ∅))
      (fkLaw_full_support G θ _) (clusterRecord G S) A =
    (law G θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent G (actualMultiClusterReveal G S) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
          (actualMultiClusterReveal_consistent S) A]
        exact frozenStateEvent_support θ (BoundaryCondition.free ∅)
          (actualMultiClusterReveal G S A) (revealRecordConfiguration G (actualMultiClusterReveal G S) A)) := by
  have he : {B | clusterRecord G S B=clusterRecord G S A} =
      revealRecordEvent G (actualMultiClusterReveal G S) A :=
    Set.ext (fun B => clusterRecord_eq_iff G S A B)
  unfold recordConditional
  congr 1

/-- Conditioning on the full preceding cluster records bounds the next
*distinct* prescribed connection by its free-law probability on the induced
unexplored graph. The geometric estimate is supplied separately. -/
theorem nextDistinct_conditional_le (θ : Parameters) (x y : ℕ → V) (j : ℕ)
    (A : Configuration G) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ (hx : x j ∈ actualMultiClusterComplementSet G (prefixSeeds x j) A)
      (hy : y j ∈ actualMultiClusterComplementSet G (prefixSeeds x j) A),
      (measure (G.induce (actualMultiClusterComplementSet G (prefixSeeds x j) A)) θ
        (BoundaryCondition.free ∅) (connectivityEvent _ ⟨x j,hx⟩ ⟨y j,hy⟩)).toReal ≤ c) :
    expectation (recordConditional (law G θ (BoundaryCondition.free ∅))
      (fkLaw_full_support G θ _) (clusterRecord G (prefixSeeds x j)) A)
      ((nextDistinctConnection G x y j).indicator fun _ => (1 : ℝ)) ≤ c := by
  let S := prefixSeeds x j
  let T := actualMultiClusterComplementSet G S A
  let P := recordConditional (law G θ (BoundaryCondition.free ∅))
    (fkLaw_full_support G θ _) (clusterRecord G S) A
  have hrec (B : Configuration G) (hB : B ∈ P.support) :
      clusterRecord G S B=clusterRecord G S A := (PMF.mem_support_filter_iff _).1 hB |>.1
  have hout (B : Configuration G) (hB : B ∈ P.support) (v : V) :
      v ∈ actualMultiClusterComplementSet G S B ↔ v ∈ T := by
    have hh := ((clusterRecord_eq_iff G S A B).1 (hrec B hB)).2
    exact not_congr (actualMultiClusterConnected_iff_of_reveal_agreement S A B hh v)
  by_cases hx : x j ∈ T
  · by_cases hy : y j ∈ T
    · let u : T := ⟨x j,hx⟩
      let v : T := ⟨y j,hy⟩
      let H := G.induce T
      let R := embeddedConfigurationRestriction H G (inducedVertexEmbedding T) (inducedVertexGraph_le G T)
      let : Fintype H.edgeSet := Fintype.ofFinite _
      have hm : P.map R=law H θ (BoundaryCondition.free ∅) := by
        rw [show P = _ from clusterRecordConditional_eq G θ S A]
        exact law_filter_actualMultiClusterRecord_map_complement_free θ S A
      have hstep : expectation P ((nextDistinctConnection G x y j).indicator fun _ => (1 : ℝ)) ≤
          expectation P (fun B => (connectivityEvent H u v).indicator (fun _ => (1 : ℝ)) (R B)) := by
        apply expectation_le_on_support
        intro B hB
        by_cases hnext : B ∈ nextDistinctConnection G x y j
        · have hclosed : ∀ a ∈ T, ∀ b, (openGraph G B).Adj a b → b ∈ T := by
            intro a ha b hab hb
            have haB := (hout B hB a).2 ha
            have hbT : b ∉ T := fun hn => hn hb
            have hbB := (hout B hB b).not.2 hbT
            obtain ⟨s,hs,hconn⟩ := Classical.not_not.1 hbB
            exact haB ⟨s,hs,hconn.trans hab.symm.reachable⟩
          have hconn : ActualConnected H (R B) u v :=
            (actualConnected_inducedRestriction G T B hclosed u v).2 hnext.1
          have hconnE : R B ∈ connectivityEvent H u v := hconn
          simp only [Set.indicator_of_mem hnext,Set.indicator_of_mem hconnE,le_refl]
        · simp only [Set.indicator_of_notMem hnext]
          by_cases hh : R B ∈ connectivityEvent H u v <;> simp [hh]
      refine hstep.trans ?_
      rw [← expectation_map,hm,← fk_measureReal_eq_expectation]
      exact hc hx hy
    · have hz : expectation P ((nextDistinctConnection G x y j).indicator fun _ => (1 : ℝ))=0 := by
        rw [← expectation_const P 0]
        apply expectation_congr_on_support
        intro B hB
        have hn : B ∉ nextDistinctConnection G x y j := by
          intro hh
          exact hy ((hout B hB (y j)).1 (nextDistinctConnection_outside G x y j B hh).2)
        simp [hn]
      exact hz ▸ hc0
  · have hz : expectation P ((nextDistinctConnection G x y j).indicator fun _ => (1 : ℝ))=0 := by
      rw [← expectation_const P 0]
      apply expectation_congr_on_support
      intro B hB
      have hn : B ∉ nextDistinctConnection G x y j := by
        intro hh
        exact hx ((hout B hB (x j)).1 (nextDistinctConnection_outside G x y j B hh).1)
      simp [hn]
    exact hz ▸ hc0

end
end PottsDiscontinuity.TorusExploration
