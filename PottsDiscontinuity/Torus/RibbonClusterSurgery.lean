module

public import PottsDiscontinuity.Torus.RibbonAttachment
public import PottsDiscontinuity.Torus.RibbonInvariantSpace

/-!
# Component counts under attachment of a closed edge

An attached ribbon imposes equality of the values at its two ends on component
functions. Rank-nullity then gives the exact cluster-count change.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

open Module

variable {N M : ℕ}

theorem ribbonFunctions_toggle_iff (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (hv : A v = false)
    (f : DirectedDart (checkerArrows N M) → ℚ) :
    f ∈ ribbonFunctions hN hM (toggleEdge A v) ↔
      f ∈ ribbonFunctions hN hM A ∧
        f (ribbonEndEquiv hN hM (v, false)) = f (ribbonEndEquiv hN hM (v, true)) := by
  let a := ribbonEndEquiv hN hM (v, false)
  let b := ribbonEndEquiv hN hM (v, true)
  have hpa : ribbonEdgePairing hN hM A a = a := by
    rw [ribbonEdgePairing_end, hv]
    rfl
  have hs : ribbonEdgePairing hN hM (toggleEdge A v) =
      Equiv.swap a b * ribbonEdgePairing hN hM A := ribbonEdgePairing_toggle hN hM A v
  constructor
  · intro hf
    have hfq : f ∈ cycleFunctions (Equiv.swap a b * ribbonEdgePairing hN hM A) := by
      rw [← hs]
      exact hf.2
    have hab : f a = f b := by
      have he := hfq a
      change f (Equiv.swap a b (ribbonEdgePairing hN hM A a)) = f a at he
      rw [hpa, Equiv.swap_apply_left] at he
      exact he.symm
    exact ⟨⟨hf.1, (cycleFunctions_swap_mul_iff _ a b f hab).mp hfq⟩, hab⟩
  · rintro ⟨hf, hab⟩
    refine ⟨hf.1, ?_⟩
    rw [hs]
    exact (cycleFunctions_swap_mul_iff _ a b f hab).mpr hf.2

/-- Component functions after attachment are the kernel of the old end-value difference. -/
def ribbonAttachmentKernelEquiv (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (hv : A v = false) :
    ribbonFunctions hN hM (toggleEdge A v) ≃ₗ[ℚ]
      LinearMap.ker (ribbonDifference hN hM A v) where
  toFun f := ⟨⟨f.val, ((ribbonFunctions_toggle_iff hN hM A v hv f.val).mp f.property).1⟩,
    sub_eq_zero.mpr ((ribbonFunctions_toggle_iff hN hM A v hv f.val).mp f.property).2⟩
  invFun f := ⟨f.val.val, (ribbonFunctions_toggle_iff hN hM A v hv f.val.val).mpr
    ⟨f.val.property, sub_eq_zero.mp f.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem clusterCount_toggle_of_connected (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (hv : A v = false)
    (h : RibbonConnected hN hM A (ribbonEndEquiv hN hM (v, false))
      (ribbonEndEquiv hN hM (v, true))) :
    clusterCount hN hM true (toggleEdge A v) = clusterCount hN hM true A := by
  rw [← finrank_ribbonFunctions, (ribbonAttachmentKernelEquiv hN hM A v hv).finrank_eq,
    ribbonDifference_eq_zero_of_connected hN hM A v h, LinearMap.ker_zero,
    finrank_top, finrank_ribbonFunctions]

theorem clusterCount_toggle_of_not_connected (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (hv : A v = false)
    (h : ¬RibbonConnected hN hM A (ribbonEndEquiv hN hM (v, false))
      (ribbonEndEquiv hN hM (v, true))) :
    clusterCount hN hM true (toggleEdge A v) + 1 = clusterCount hN hM true A := by
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero
    (ribbonDifference_ne_zero_of_not_connected hN hM A v h)
  rw [← (ribbonAttachmentKernelEquiv hN hM A v hv).finrank_eq,
    finrank_ribbonFunctions, finrank_ribbonFunctions] at hd
  exact hd

theorem clusterCount_toggle_of_reachable (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (hv : A v = false)
    (h : (diamondOpenGraph hN hM true A).Reachable
      (faceEndpoint hN hM true v false) (faceEndpoint hN hM true v true)) :
    clusterCount hN hM true (toggleEdge A v) = clusterCount hN hM true A := by
  apply clusterCount_toggle_of_connected hN hM A v hv
  apply (ribbonConnected_iff_reachable hN hM A _ _).mpr
  simpa only [ribbonFace_end] using h

theorem clusterCount_toggle_of_not_reachable (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (hv : A v = false)
    (h : ¬(diamondOpenGraph hN hM true A).Reachable
      (faceEndpoint hN hM true v false) (faceEndpoint hN hM true v true)) :
    clusterCount hN hM true (toggleEdge A v) + 1 = clusterCount hN hM true A := by
  apply clusterCount_toggle_of_not_connected hN hM A v hv
  intro he
  apply h
  simpa only [ribbonFace_end] using ribbonConnected_reachable hN hM A he

end PottsDiscontinuity.Torus
