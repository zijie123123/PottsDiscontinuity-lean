module

public import PottsDiscontinuity.Torus.RibbonSurgery

/-!
# The empty ribbon subgraph

Every primal vertex is an isolated disc, with one boundary component. These
identifications provide the base case for the cellular attachment argument.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The configuration with every indexed primal edge closed. -/
def closedRCConfig (N M : ℕ) : RCConfig N M := fun _ => false

theorem diamondOpenGraph_closed (hN : Even N) (hM : Even M) (c : Bool) :
    diamondOpenGraph hN hM c (closedRCConfig N M) = ⊥ := by
  ext u v
  simp only [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj, closedRCConfig,
    Bool.false_eq_true, false_and, exists_false, Set.mem_ofPred_eq, SimpleGraph.bot_adj]

/-- The components of the empty indexed graph are its actual vertices. -/
def closedClusterEquiv (hN : Even N) (hM : Even M) (c : Bool) :
    (diamondOpenGraph hN hM c (closedRCConfig N M)).ConnectedComponent ≃
      FaceVertex N M c where
  toFun := Quot.lift id (fun u v h => by
    rw [diamondOpenGraph_closed, SimpleGraph.reachable_bot] at h
    exact h)
  invFun := (diamondOpenGraph hN hM c (closedRCConfig N M)).connectedComponentMk
  left_inv x := Quot.inductionOn x (fun _ => rfl)
  right_inv _ := rfl

theorem clusterCount_closed (hN : Even N) (hM : Even M) (c : Bool) :
    clusterCount hN hM c (closedRCConfig N M) = Fintype.card (FaceVertex N M c) := by
  rw [clusterCount, Nat.card_congr (closedClusterEquiv hN hM c), Nat.card_eq_fintype_card]

theorem ribbonBoundary_closed (hN : Even N) (hM : Even M) :
    ribbonBoundary hN hM (closedRCConfig N M) = faceRotation hN hM := by
  have he : ribbonEdgePairing hN hM (closedRCConfig N M) = 1 := by
    apply Equiv.ext
    intro d
    exact (ribbonEdgePairing_eq_self_iff hN hM _ d).mpr rfl
  rw [ribbonBoundary, he]
  rfl

/-- Empty-subgraph boundary cycles correspond individually to primal vertex discs. -/
def faceRotationCycleEquiv (hN : Even N) (hM : Even M) :
    PermutationCycle (faceRotation hN hM) ≃ FaceVertex N M true where
  toFun := Quotient.lift (ribbonFace hN hM) (fun d e h =>
    Subtype.ext ((sameCycle_faceRotation hN hM d e).mp h))
  invFun v := Quotient.mk _ (ribbonVertexDart hN hM v)
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro d
    apply Quotient.sound
    apply (sameCycle_faceRotation hN hM _ _).mpr
    exact congrArg Subtype.val (ribbonFace_vertexDart hN hM (ribbonFace hN hM d))
  right_inv v := ribbonFace_vertexDart hN hM v

theorem rcLoopCount_closed (hN : Even N) (hM : Even M) :
    rcLoopCount hN hM (closedRCConfig N M) = Fintype.card (FaceVertex N M true) := by
  rw [← permutationCycleCount_ribbonBoundary, ribbonBoundary_closed,
    permutationCycleCount, Nat.card_congr (faceRotationCycleEquiv hN hM),
    Nat.card_eq_fintype_card]

@[simp] theorem openCount_closed : openCount (closedRCConfig N M) = 0 := by
  simp only [openCount, closedRCConfig, Bool.false_eq_true, Finset.filter_false,
    Finset.card_empty]

end PottsDiscontinuity.Torus
