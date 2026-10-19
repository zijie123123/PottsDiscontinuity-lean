module

public import PottsDiscontinuity.Torus.RibbonIntersection

/-!
# Cellular boundaries are the intersection radical

For a capped boundary, its corner primitive differs from the boundary-cycle value
by one potential per primal vertex. Its intersection coefficient is therefore a
vertex coboundary and pairs to zero with every conserved flow.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem ribbonBoundaryOf_pairing (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (d : DirectedDart (checkerArrows N M)) :
    ribbonBoundaryOf hN hM A (ribbonEdgePairing hN hM A d) =
      ribbonBoundaryOf hN hM A ((faceRotation hN hM).symm d) := by
  have he := ribbonBoundaryOf_step hN hM A ((faceRotation hN hM).symm d)
  change ribbonBoundaryOf hN hM A
    (ribbonEdgePairing hN hM A (faceRotation hN hM ((faceRotation hN hM).symm d))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  exact he

theorem ribbonHalfFlow_faceBoundary (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (F : RibbonBoundaryComponent hN hM A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM A (ribbonFaceBoundary hN hM A F) d =
      F (ribbonBoundaryOf hN hM A (ribbonEdgePairing hN hM A d)) -
        F (ribbonBoundaryOf hN hM A d) := by
  obtain ⟨⟨v, b⟩, rfl⟩ := (ribbonEndEquiv hN hM).surjective d
  rw [ribbonHalfFlow_end, ribbonEdgePairing_end]
  cases ha : A v
  · simp only [extendDiamondChain_closed A _ v ha, neg_zero, ite_self, Bool.false_xor, sub_self]
  · rw [extendDiamondChain_open A _ v ha]
    have hc : ribbonFaceBoundary hN hM A F ⟨v, ha⟩ =
        F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (v, true))) -
          F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (v, false))) := rfl
    rw [hc]
    cases b <;> simp only [Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_true, ite_false]
    all_goals ring

theorem exists_intersection_potential_of_faceBoundary (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : diamondCycleSpace hN hM A)
    (F : RibbonBoundaryComponent hN hM A → ℚ) (hF : ribbonFaceBoundary hN hM A F = f.val) :
    ∃ g : FaceVertex N M true → ℚ,
      diamondCoboundary hN hM A g = ribbonIntersectionCoefficient hN hM A f := by
  let H := fun d => ribbonCornerPrimitive hN hM A f d - F (ribbonBoundaryOf hN hM A d)
  have hi : ∀ d, H ((faceRotation hN hM).symm d) = H d := by
    intro d
    have hr := ribbonCornerPrimitive_rotation_sub hN hM A f d
    have hb := ribbonHalfFlow_faceBoundary hN hM A F d
    rw [hF, ribbonBoundaryOf_pairing] at hb
    dsimp [H]
    linarith
  have hs : ∀ d, H (faceRotation hN hM d) = H d := by
    intro d
    have he := hi (faceRotation hN hM d)
    rw [Equiv.symm_apply_apply] at he
    exact he.symm
  let g := fun v => H (ribbonVertexDart hN hM v)
  have hg : ∀ d, H d = g (ribbonFace hN hM d) := by
    intro d
    apply sameCycle_invariant (faceRotation hN hM) H hs
    apply (sameCycle_faceRotation hN hM _ _).mpr
    exact congrArg Subtype.val (ribbonFace_vertexDart hN hM (ribbonFace hN hM d)).symm
  refine ⟨g, ?_⟩
  funext e
  have h₀ := hg (ribbonEndEquiv hN hM (e.val, false))
  have h₁ := hg (ribbonEndEquiv hN hM (e.val, true))
  simp only [ribbonFace_end] at h₀ h₁
  have he := congrFun hF e
  change F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, true))) -
    F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, false))) = f.val e at he
  change g (faceEndpoint hN hM true e.val true) - g (faceEndpoint hN hM true e.val false) =
    ribbonCornerPrimitive hN hM A f (ribbonEndEquiv hN hM (e.val, true)) -
      ribbonCornerPrimitive hN hM A f (ribbonEndEquiv hN hM (e.val, false)) - f.val e
  dsimp [H] at h₀ h₁
  linarith

/-- Every actual capped boundary pairs to zero with every conserved indexed flow. -/
theorem ribbonIntersection_zero_of_mem_boundary (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f g : diamondCycleSpace hN hM A)
    (hf : f ∈ ribbonBoundarySpace hN hM A) : ribbonIntersection hN hM A f g = 0 := by
  obtain ⟨F, he⟩ := hf
  have hF : ribbonFaceBoundary hN hM A F = f.val := congrArg Subtype.val he
  obtain ⟨p, hp⟩ := exists_intersection_potential_of_faceBoundary hN hM A f F hF
  unfold ribbonIntersection
  rw [← hp]
  have he := diamondBoundary_pairing hN hM A p g.val
  have hz : diamondBoundary hN hM A g.val = 0 := g.property
  rw [hz] at he
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
  exact he.symm

end PottsDiscontinuity.Torus
