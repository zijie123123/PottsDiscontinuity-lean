module

public import PottsDiscontinuity.Torus.DiamondCycleAnnihilator
public import PottsDiscontinuity.Torus.RibbonCornerPrimitive
public import PottsDiscontinuity.Torus.RibbonHomology

/-!
# The cyclic-order intersection coefficient

The corner primitive measures the separation between the two sides of an indexed
ribbon. Subtracting its own flow gives the intersection coefficient. A coefficient
annihilating every conserved flow is a vertex potential, and correcting by that
potential reconstructs an actual capped boundary.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The edge coefficient of the cyclic-order intersection form. -/
def ribbonIntersectionCoefficient (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (e : OpenDiamondEdge A) : ℚ :=
  ribbonCornerPrimitive hN hM A f (ribbonEndEquiv hN hM (e.val, true)) -
    ribbonCornerPrimitive hN hM A f (ribbonEndEquiv hN hM (e.val, false)) - f.val e

/-- The cyclic-order intersection pairing on actual conserved indexed flows. -/
def ribbonIntersection (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) : ℚ :=
  ∑ e, ribbonIntersectionCoefficient hN hM A f e * g.val e

/-- Compatible corner primitives along vertices and ribbons descend to boundary cycles. -/
theorem exists_ribbonFaceFunction_of_primitive (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : diamondCycleSpace hN hM A)
    (D : DirectedDart (checkerArrows N M) → ℚ)
    (hR : ∀ d, D ((faceRotation hN hM).symm d) - D d = ribbonHalfFlow hN hM A f.val d)
    (hE : ∀ d, D (ribbonEdgePairing hN hM A d) - D d = ribbonHalfFlow hN hM A f.val d) :
    ∃ F : RibbonBoundaryComponent hN hM A → ℚ, ribbonFaceBoundary hN hM A F = f.val := by
  have hp : ∀ d, D (ribbonBoundary hN hM A d) = D d := by
    intro d
    have hr := hR (faceRotation hN hM d)
    have he := hE (faceRotation hN hM d)
    rw [Equiv.symm_apply_apply] at hr
    change D (ribbonEdgePairing hN hM A (faceRotation hN hM d)) = D d
    linarith
  let F : RibbonBoundaryComponent hN hM A → ℚ :=
    Quotient.lift D (fun _ _ h => sameCycle_invariant _ D hp h)
  refine ⟨F, ?_⟩
  funext e
  have he := hE (ribbonEndEquiv hN hM (e.val, false))
  rw [ribbonEdgePairing_end, e.property, ribbonHalfFlow_end,
    extendDiamondChain_open A f.val e.val e.property] at he
  exact he

/-- A potential intersection coefficient can be removed by shifting each vertex primitive. -/
theorem exists_ribbonFaceFunction_of_intersection_potential (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : diamondCycleSpace hN hM A) (g : FaceVertex N M true → ℚ)
    (hg : diamondCoboundary hN hM A g = ribbonIntersectionCoefficient hN hM A f) :
    ∃ F : RibbonBoundaryComponent hN hM A → ℚ, ribbonFaceBoundary hN hM A F = f.val := by
  let D := fun d => ribbonCornerPrimitive hN hM A f d - g (ribbonFace hN hM d)
  apply exists_ribbonFaceFunction_of_primitive hN hM A f D
  · intro d
    have he := ribbonCornerPrimitive_rotation_sub hN hM A f d
    have hf : ribbonFace hN hM ((faceRotation hN hM).symm d) = ribbonFace hN hM d :=
      Subtype.ext ((sameCycle_faceRotation hN hM _ _).mp
        (Equiv.Perm.SameCycle.rfl.symm_apply_left))
    dsimp [D]
    rw [hf]
    linarith
  · intro d
    obtain ⟨⟨v, b⟩, rfl⟩ := (ribbonEndEquiv hN hM).surjective d
    rw [ribbonEdgePairing_end, ribbonHalfFlow_end]
    cases ha : A v
    · simp only [Bool.false_xor, extendDiamondChain_closed A f.val v ha,
        neg_zero, ite_self, sub_self]
    · have he := congrFun hg (⟨v, ha⟩ : OpenDiamondEdge A)
      change g (faceEndpoint hN hM true v true) - g (faceEndpoint hN hM true v false) =
        ribbonCornerPrimitive hN hM A f (ribbonEndEquiv hN hM (v, true)) -
          ribbonCornerPrimitive hN hM A f (ribbonEndEquiv hN hM (v, false)) - f.val ⟨v, ha⟩ at he
      rw [extendDiamondChain_open A f.val v ha]
      cases b <;> simp only [Bool.true_xor, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ite_false, ite_true]
      all_goals dsimp [D]; simp only [ribbonFace_end]; linarith

/-- The radical of the intersection pairing is contained in the actual cellular boundaries. -/
theorem mem_ribbonBoundarySpace_of_intersection_zero (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : diamondCycleSpace hN hM A)
    (h : ∀ g : diamondCycleSpace hN hM A, ribbonIntersection hN hM A f g = 0) :
    f ∈ ribbonBoundarySpace hN hM A := by
  obtain ⟨g, hg⟩ := exists_diamondPotential_of_cycle_annihilator hN hM A
    (ribbonIntersectionCoefficient hN hM A f) h
  obtain ⟨F, hF⟩ := exists_ribbonFaceFunction_of_intersection_potential hN hM A f g hg
  exact ⟨F, Subtype.ext hF⟩

end PottsDiscontinuity.Torus
