module

public import PottsDiscontinuity.CorrLength.RotatedFreeLimit
public import PottsDiscontinuity.TorusRC.LiftedBoxes

/-! # Translation invariance of native lifted free-box probabilities -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open CorrLength

/-- Recenter a lifted lattice point by the displacement d-c. -/
def liftedRecenter (c d z : RotatedVertex) : RotatedVertex :=
  ⟨(z.val.1 - c.val.1 + d.val.1, z.val.2 - c.val.2 + d.val.2), by
    convert (z.property.sub c.property).add d.property using 1; ring⟩

theorem inLiftedBox_recenter_iff (c d z : RotatedVertex) (R : ℕ) :
    inLiftedBox R d (liftedRecenter c d z) ↔ inLiftedBox R c z := by
  simp [inLiftedBox, liftedRecenter]

theorem liftedRecenter_inverse (c d z : RotatedVertex) :
    liftedRecenter d c (liftedRecenter c d z) = z := by
  apply Subtype.ext
  ext <;> dsimp [liftedRecenter] <;> ring

def liftedBoxRecenterIso (c d : RotatedVertex) (R : ℕ) :
    liftedBoxGraph c R ≃g liftedBoxGraph d R where
  toEquiv :=
    { toFun := fun z => ⟨liftedRecenter c d z.val,
        (inLiftedBox_recenter_iff c d z.val R).mpr z.property⟩
      invFun := fun z => ⟨liftedRecenter d c z.val,
        (inLiftedBox_recenter_iff d c z.val R).mpr z.property⟩
      left_inv := fun z => Subtype.ext (liftedRecenter_inverse c d z.val)
      right_inv := fun z => Subtype.ext (liftedRecenter_inverse d c z.val) }
  map_rel_iff' := by
    intro u v
    change rotatedLattice.Adj (liftedRecenter c d u.val) (liftedRecenter c d v.val) ↔
      rotatedLattice.Adj u.val v.val
    have hx : (liftedRecenter c d u.val).val.1 - (liftedRecenter c d v.val).val.1 =
        u.val.val.1 - v.val.val.1 := by dsimp [liftedRecenter]; ring
    have hy : (liftedRecenter c d u.val).val.2 - (liftedRecenter c d v.val).val.2 =
        u.val.val.2 - v.val.val.2 := by dsimp [liftedRecenter]; ring
    change (|_| = 1 ∧ |_| = 1) ↔ _
    rw [hx, hy]
    rfl

noncomputable local instance recenterBoxEdges (c : RotatedVertex) (R : ℕ) :
    Fintype (liftedBoxGraph c R).edgeSet := Fintype.ofFinite _
noncomputable local instance recenterBoxEdgeDecidableEq (c : RotatedVertex) (R : ℕ) :
    DecidableEq (liftedBoxGraph c R).edgeSet := Classical.decEq _

noncomputable section

/-- Recentring transports the exact free law and the sampled connection event. -/
theorem liftedBoxFreeConnectionProbability_recenter (θ : FK.Parameters)
    (c d u v : RotatedVertex) (R : ℕ) :
    liftedBoxFreeConnectionProbability θ d R (liftedRecenter c d u) (liftedRecenter c d v) =
      liftedBoxFreeConnectionProbability θ c R u v := by
  classical
  let e := liftedBoxRecenterIso c d R
  have hlaw := FK.law_configurationIso_map θ e (FK.BoundaryCondition.free ∅)
  rw [FK.boundaryConditionIso_free_empty] at hlaw
  unfold liftedBoxFreeConnectionProbability torusRCFiberEventProbability
  rw [← hlaw, FK.FiniteProbability.expectation_map]
  apply congrArg (FK.FiniteProbability.expectation _)
  funext A
  have hevent : FK.configurationIso e A ∈
      liftedBoxFreeConnectionEvent d R (liftedRecenter c d u) (liftedRecenter c d v) ↔
      A ∈ liftedBoxFreeConnectionEvent c R u v := by
    constructor
    · rintro ⟨hu,hv,hconn⟩
      have hu' := (inLiftedBox_recenter_iff c d u R).mp hu
      have hv' := (inLiftedBox_recenter_iff c d v R).mp hv
      exact ⟨hu',hv', (FK.actualConnected_configurationIso e A ⟨u,hu'⟩ ⟨v,hv'⟩).mp hconn⟩
    · rintro ⟨hu,hv,hconn⟩
      exact ⟨(inLiftedBox_recenter_iff c d u R).mpr hu,
        (inLiftedBox_recenter_iff c d v R).mpr hv,
        (FK.actualConnected_configurationIso e A ⟨u,hu⟩ ⟨v,hv⟩).mpr hconn⟩
  by_cases hA : A ∈ liftedBoxFreeConnectionEvent c R u v <;>
    simp [Set.indicator, hevent, hA]

/-- All complete 2n blocks in the source chain have the same native free-box
connection probability, centered at the origin. -/
theorem liftedBoxFreeConnectionProbability_chain (θ : FK.Parameters)
    (x : ℤ) (hx : Even x) (n j R : ℕ) :
    liftedBoxFreeConnectionProbability θ (liftedChainSite x hx n j) R
      (liftedChainSite x hx n j) (liftedChainSite x hx n (j + 1)) =
      liftedBoxFreeConnectionProbability θ rotatedLatticeOrigin R
        rotatedLatticeOrigin (rotatedDiagonalSite n) := by
  have h := liftedBoxFreeConnectionProbability_recenter θ
    (liftedChainSite x hx n j) rotatedLatticeOrigin
    (liftedChainSite x hx n j) (liftedChainSite x hx n (j + 1)) R
  have hc : liftedRecenter (liftedChainSite x hx n j) rotatedLatticeOrigin
      (liftedChainSite x hx n j) = rotatedLatticeOrigin := by
    apply Subtype.ext
    simp [liftedRecenter]
  have hv : liftedRecenter (liftedChainSite x hx n j) rotatedLatticeOrigin
      (liftedChainSite x hx n (j + 1)) = rotatedDiagonalSite n := by
    apply Subtype.ext
    ext <;> dsimp [liftedRecenter, liftedChainSite, liftedColumnSite,
      rotatedLatticeOrigin, rotatedDiagonalSite] <;> ring
  rw [hc,hv] at h
  exact h.symm

end

end PottsDiscontinuity.TorusRC
