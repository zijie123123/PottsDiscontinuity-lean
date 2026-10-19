module

public import PottsDiscontinuity.Torus.RibbonConnectivity
public import PottsDiscontinuity.TorusRC.PeriodicReflection
public import PottsDiscontinuity.TorusTopology.LiftedEdgeCover

/-! # Reflection of the diamond torus endpoints -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength TorusTopology

variable {N M : ℕ}

/-- The canonical integer representative of a primal face. -/
def canonicalPrimalLift (v : FaceVertex N M true) : RotatedVertex :=
  ⟨((v.val.1.val : ℤ), (v.val.2.val : ℤ)), by
    have hp : (v.val.1.val + v.val.2.val) % 2 = 0 := by
      simpa only [checker, decide_eq_true_eq] using v.property
    change Even ((v.val.1.val : ℤ) + (v.val.2.val : ℤ))
    exact_mod_cast (Nat.even_iff.mpr hp)⟩

def reflectPrimalFace (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (t : ℤ) (ht : Even t) (v : FaceVertex N M true) : FaceVertex N M true :=
  liftedFaceVertex hN hM hNp hMp (liftedHorizontalReflect t ht (canonicalPrimalLift v))

theorem reflectPrimalFace_val (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (t : ℤ) (ht : Even t) (v : FaceVertex N M true) :
    (reflectPrimalFace hN hM hNp hMp t ht v).val =
      (v.val.1, periodicReflect hMp t v.val.2) := by
  apply Prod.ext
  · exact periodicCoordinate_nat hNp v.val.1
  · rfl

def reflectPrimalFaceEquiv (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (t : ℤ) (ht : Even t) : FaceVertex N M true ≃ FaceVertex N M true where
  toFun := reflectPrimalFace hN hM hNp hMp t ht
  invFun := reflectPrimalFace hN hM hNp hMp t ht
  left_inv v := by
    apply Subtype.ext
    rw [reflectPrimalFace_val, reflectPrimalFace_val]
    exact Prod.ext rfl ((periodicReflect hMp t).left_inv v.val.2)
  right_inv v := by
    apply Subtype.ext
    rw [reflectPrimalFace_val, reflectPrimalFace_val]
    exact Prod.ext rfl ((periodicReflect hMp t).left_inv v.val.2)

theorem reflectPrimalFace_projects (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (t : ℤ) (ht : Even t) (u : RotatedVertex) :
    reflectPrimalFace hN hM hNp hMp t ht (liftedFaceVertex hN hM hNp hMp u) =
      liftedFaceVertex hN hM hNp hMp (liftedHorizontalReflect t ht u) := by
  apply Subtype.ext
  rw [reflectPrimalFace_val]
  exact Prod.ext rfl (periodicReflect_periodicCoordinate hMp t u.val.2)

/-- The actual indexed edge reflection has its offset t+1, while primal
vertices reflect with offset t. This retains the midpoint convention. -/
def reflectEdgeIndex (hMp : 0 < M) (t : ℤ) : (Fin N × Fin M) ≃ (Fin N × Fin M) :=
  Equiv.prodCongr (Equiv.refl _) (periodicReflect hMp (t + 1))

theorem reflectPrimalFace_edge (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (t : ℤ) (ht : Even t) (e : Fin N × Fin M) :
    s(reflectPrimalFace hN hM hNp hMp t ht (faceEndpoint hN hM true e false),
      reflectPrimalFace hN hM hNp hMp t ht (faceEndpoint hN hM true e true)) =
    s(faceEndpoint hN hM true (reflectEdgeIndex hMp t e) false,
      faceEndpoint hN hM true (reflectEdgeIndex hMp t e) true) := by
  rw [← edgeLift_projects hN hM hNp hMp e false,
    ← edgeLift_projects hN hM hNp hMp e true,
    reflectPrimalFace_projects, reflectPrimalFace_projects]
  have h := liftedFaceEndpoints_eq hN hM hNp hMp
    (liftedHorizontalReflect t ht (edgeLift e false))
    (liftedHorizontalReflect t ht (edgeLift e true))
    (liftedHorizontalReflect_adj t ht (edgeLift_adj e))
  rw [liftedHorizontalReflect_index hNp hMp t ht (edgeLift_adj e), edgeLift_index] at h
  exact h

theorem reflectEdgeIndex_involutive (hMp : 0 < M) (t : ℤ) :
    Function.Involutive (reflectEdgeIndex (N := N) hMp t) := by
  intro e
  exact Prod.ext rfl ((periodicReflect hMp (t + 1)).left_inv e.2)

def reflectRCConfig (hMp : 0 < M) (t : ℤ) (A : RCConfig N M) : RCConfig N M :=
  fun e => A (reflectEdgeIndex hMp t e)

theorem reflectRCConfig_involutive (hMp : 0 < M) (t : ℤ) :
    Function.Involutive (reflectRCConfig (N := N) hMp t) := by
  intro A
  funext e
  exact congrArg A (reflectEdgeIndex_involutive hMp t e)

theorem diamondOpenGraph_reflect_adj (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (t : ℤ) (ht : Even t) (A : RCConfig N M)
    {u v : FaceVertex N M true} (huv : (diamondOpenGraph hN hM true A).Adj u v) :
    (diamondOpenGraph hN hM true (reflectRCConfig hMp t A)).Adj
      (reflectPrimalFace hN hM hNp hMp t ht u) (reflectPrimalFace hN hM hNp hMp t ht v) := by
  rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at huv ⊢
  obtain ⟨⟨e,he,hpair⟩,hne⟩ := huv
  refine ⟨⟨reflectEdgeIndex hMp t e, ?_, ?_⟩,
    (reflectPrimalFaceEquiv hN hM hNp hMp t ht).injective.ne hne⟩
  · simpa only [reflectRCConfig, reflectEdgeIndex_involutive hMp t e] using he
  · have h := congrArg (Sym2.map (reflectPrimalFace hN hM hNp hMp t ht)) hpair
    simp only [Sym2.map_mk] at h
    exact h.trans (reflectPrimalFace_edge hN hM hNp hMp t ht e)

/-- Horizontal reflection is an isomorphism of the actual open primal graphs. -/
def diamondReflectIso (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (t : ℤ) (ht : Even t) (A : RCConfig N M) :
    diamondOpenGraph hN hM true A ≃g
      diamondOpenGraph hN hM true (reflectRCConfig hMp t A) where
  toEquiv := reflectPrimalFaceEquiv hN hM hNp hMp t ht
  map_rel_iff' := by
    intro u v
    constructor
    · intro h
      have h' := diamondOpenGraph_reflect_adj hN hM hNp hMp t ht _ h
      change (diamondOpenGraph hN hM true (reflectRCConfig hMp t (reflectRCConfig hMp t A))).Adj
        ((reflectPrimalFaceEquiv hN hM hNp hMp t ht).symm
          (reflectPrimalFaceEquiv hN hM hNp hMp t ht u))
        ((reflectPrimalFaceEquiv hN hM hNp hMp t ht).symm
          (reflectPrimalFaceEquiv hN hM hNp hMp t ht v)) at h'
      simpa only [reflectRCConfig_involutive hMp t A, Equiv.symm_apply_apply] using h'
    · exact diamondOpenGraph_reflect_adj hN hM hNp hMp t ht A

theorem clusterCount_reflect (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (t : ℤ) (ht : Even t) (A : RCConfig N M) :
    clusterCount hN hM true (reflectRCConfig hMp t A) = clusterCount hN hM true A :=
  Nat.card_congr (diamondReflectIso hN hM hNp hMp t ht A).connectedComponentEquiv.symm

end PottsDiscontinuity.TorusRC
