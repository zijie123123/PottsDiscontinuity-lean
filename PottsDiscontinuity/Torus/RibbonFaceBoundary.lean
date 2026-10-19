module

public import PottsDiscontinuity.Torus.DiamondChains
public import PottsDiscontinuity.Torus.RibbonInvariantSpace
public import PottsDiscontinuity.Torus.RibbonSurgery

/-!
# Boundaries of the capped ribbon faces

The coefficient on an indexed ribbon is the difference of the values assigned to
the boundary cycles on its two sides. The kernel consists exactly of one value per
ribbon component, so the image has dimension ell minus k.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

open Module

variable {N M : ℕ}

/-- The actual ribbon boundary component containing a corner. -/
def ribbonBoundaryOf (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (d : DirectedDart (checkerArrows N M)) : RibbonBoundaryComponent hN hM A :=
  Quotient.mk _ d

@[simp] theorem ribbonBoundaryOf_step (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (d : DirectedDart (checkerArrows N M)) :
    ribbonBoundaryOf hN hM A (ribbonBoundary hN hM A d) = ribbonBoundaryOf hN hM A d := by
  exact Quotient.sound (Equiv.Perm.SameCycle.rfl.apply_left)

/-- Signed boundary chains of the capped ribbon faces, on the indexed open edges. -/
def ribbonFaceBoundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    (RibbonBoundaryComponent hN hM A → ℚ) →ₗ[ℚ] (OpenDiamondEdge A → ℚ) where
  toFun f e := f (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, true))) -
    f (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, false)))
  map_add' f g := by ext e; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem ribbonFaceBoundary_kernel_pairing (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : LinearMap.ker (ribbonFaceBoundary hN hM A))
    (d : DirectedDart (checkerArrows N M)) :
    f.val (ribbonBoundaryOf hN hM A (ribbonEdgePairing hN hM A d)) =
      f.val (ribbonBoundaryOf hN hM A d) := by
  obtain ⟨⟨v, b⟩, rfl⟩ := (ribbonEndEquiv hN hM).surjective d
  rw [ribbonEdgePairing_end]
  cases ha : A v
  · rw [Bool.false_xor]
  · have he := congrFun f.property (⟨v, ha⟩ : OpenDiamondEdge A)
    change f.val (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (v, true))) -
      f.val (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (v, false))) = 0 at he
    cases b
    · exact sub_eq_zero.mp he
    · exact (sub_eq_zero.mp he).symm

/-- Zero face boundaries are precisely functions on the connected ribbon components. -/
def ribbonFaceBoundaryKernelEquiv (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    LinearMap.ker (ribbonFaceBoundary hN hM A) ≃ₗ[ℚ] ribbonFunctions hN hM A where
  toFun f := ⟨fun d => f.val (ribbonBoundaryOf hN hM A d), by
    constructor
    · intro d
      calc
        f.val (ribbonBoundaryOf hN hM A (faceRotation hN hM d)) =
            f.val (ribbonBoundaryOf hN hM A
              (ribbonEdgePairing hN hM A (faceRotation hN hM d))) :=
          (ribbonFaceBoundary_kernel_pairing hN hM A f _).symm
        _ = f.val (ribbonBoundaryOf hN hM A d) :=
          congrArg f.val (ribbonBoundaryOf_step hN hM A d)
    · exact ribbonFaceBoundary_kernel_pairing hN hM A f⟩
  invFun f := ⟨Quotient.lift f.val (fun _ _ h => ribbonFunctions_invariant hN hM A f
    (ribbonConnected_of_boundary_sameCycle hN hM A h)), by
    funext e
    have he := f.property.2 (ribbonEndEquiv hN hM (e.val, false))
    rw [ribbonEdgePairing_end, e.property] at he
    exact sub_eq_zero.mpr he⟩
  left_inv f := by
    apply Subtype.ext
    funext q
    exact Quotient.inductionOn q (fun _ => rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem finrank_ker_ribbonFaceBoundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    finrank ℚ (LinearMap.ker (ribbonFaceBoundary hN hM A)) = clusterCount hN hM true A := by
  rw [(ribbonFaceBoundaryKernelEquiv hN hM A).finrank_eq, finrank_ribbonFunctions]

/-- The capped boundary image has dimension ell minus k, expressed without subtraction. -/
theorem finrank_range_ribbonFaceBoundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    finrank ℚ (LinearMap.range (ribbonFaceBoundary hN hM A)) + clusterCount hN hM true A =
      rcLoopCount hN hM A := by
  let : Fintype (RibbonBoundaryComponent hN hM A) := Fintype.ofFinite _
  have he := LinearMap.finrank_range_add_finrank_ker (ribbonFaceBoundary hN hM A)
  rw [finrank_ker_ribbonFaceBoundary, Module.finrank_pi,
    ← Nat.card_eq_fintype_card, card_ribbonBoundaryComponent] at he
  exact he

end PottsDiscontinuity.Torus
