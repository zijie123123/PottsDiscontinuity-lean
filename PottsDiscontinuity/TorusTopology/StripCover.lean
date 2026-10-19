module

public import PottsDiscontinuity.TorusTopology.LiftedEdgeCover
public import PottsDiscontinuity.TorusRC.CylinderEvents

/-! Lifting the finite annular strip while retaining its horizontal coordinates.
The vertical coordinate is unwrapped, so a finite-strip crossing gives the exact
lifted event used in the barrier event B (`TorusRC.torusRCBarrier`). -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC CorrLength
variable {N M : ℕ}

/-- The representative with both coordinates in the fundamental rectangle. -/
def faceLift (u : FaceVertex N M true) : RotatedVertex :=
  ⟨((u.val.1.val : ℤ),(u.val.2.val : ℤ)),by
    have he : Even (u.val.1.val+u.val.2.val) := Nat.even_iff.2 (by
      simpa only [checker,decide_eq_true_eq] using u.property)
    change Even ((u.val.1.val : ℤ)+(u.val.2.val : ℤ))
    exact_mod_cast he⟩

lemma faceLift_projects (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (u : FaceVertex N M true) : liftedFaceVertex hN hM hNp hMp (faceLift u) = u := by
  apply Subtype.ext
  exact Prod.ext (periodicCoordinate_nat hNp u.val.1) (periodicCoordinate_nat hMp u.val.2)

/-- The finite vertical annular strip, with horizontal seam edges removed.
Vertical seam edges are retained. -/
def finiteStripGraph (hN : Even N) (hM : Even M) (A : RCConfig N M) (K : ℕ) :
    SimpleGraph (FaceVertex N M true) :=
  SimpleGraph.fromEdgeSet {p | ∃ e : Fin N × Fin M, A e = true ∧ e.1.val ≠ 0 ∧
    (faceEndpoint hN hM true e false).val.1.val ≤ K ∧
    (faceEndpoint hN hM true e true).val.1.val ≤ K ∧
    p = s(faceEndpoint hN hM true e false,faceEndpoint hN hM true e true)}

/-- Lift one indexed strip edge from any prescribed lift of its initial vertex. -/
theorem finiteStrip_adj_lifts (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (K : ℕ) {u v : FaceVertex N M true}
    (huv : (finiteStripGraph hN hM A K).Adj u v)
    (u' : RotatedVertex) (hproj : liftedFaceVertex hN hM hNp hMp u' = u)
    (hux : u'.val.1 = (u.val.1.val : ℤ)) :
    ∃ v' : RotatedVertex, (liftedStripGraph hNp hMp A 0 (K : ℤ)).Adj u' v' ∧
      liftedFaceVertex hN hM hNp hMp v' = v ∧ v'.val.1 = (v.val.1.val : ℤ) := by
  rw [finiteStripGraph,SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨e,he,hx,hf,ht,hep⟩,_⟩ := huv
  rcases Sym2.eq_iff.1 hep with h | h
  · rcases h with ⟨rfl,rfl⟩
    obtain ⟨k,hk⟩ := exists_deck_edgeLift_of_projection hN hM hNp hMp e hx false u' hproj hux
    refine ⟨verticalDeck hM k (edgeLift e true),?_,?_,?_⟩
    · rw [← hk]
      refine ⟨verticalDeck_adj hM k (edgeLift_adj e),?_,?_,?_⟩
      · rw [verticalDeck_index,edgeLift_index]
        exact he
      · change 0 ≤ (edgeLift e false).val.1 ∧ (edgeLift e false).val.1 ≤ (K : ℤ)
        rw [edgeLift_x e hx false hN hM]
        exact ⟨by positivity,by exact_mod_cast hf⟩
      · change 0 ≤ (edgeLift e true).val.1 ∧ (edgeLift e true).val.1 ≤ (K : ℤ)
        rw [edgeLift_x e hx true hN hM]
        exact ⟨by positivity,by exact_mod_cast ht⟩
    · rw [verticalDeck_projects,edgeLift_projects]
    · exact edgeLift_x e hx true hN hM
  · rcases h with ⟨rfl,rfl⟩
    obtain ⟨k,hk⟩ := exists_deck_edgeLift_of_projection hN hM hNp hMp e hx true u' hproj hux
    refine ⟨verticalDeck hM k (edgeLift e false),?_,?_,?_⟩
    · rw [← hk]
      refine ⟨verticalDeck_adj hM k (edgeLift_adj e).symm,?_,?_,?_⟩
      · rw [verticalDeck_index,liftedEdgeIndex_comm,edgeLift_index]
        exact he
      · change 0 ≤ (edgeLift e true).val.1 ∧ (edgeLift e true).val.1 ≤ (K : ℤ)
        rw [edgeLift_x e hx true hN hM]
        exact ⟨by positivity,by exact_mod_cast ht⟩
      · change 0 ≤ (edgeLift e false).val.1 ∧ (edgeLift e false).val.1 ≤ (K : ℤ)
        rw [edgeLift_x e hx false hN hM]
        exact ⟨by positivity,by exact_mod_cast hf⟩
    · rw [verticalDeck_projects,edgeLift_projects]
    · exact edgeLift_x e hx false hN hM

/-- A finite annular walk lifts from any specified initial lift. -/
theorem finiteStrip_walk_lifts (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (K : ℕ) {u v : FaceVertex N M true}
    (p : (finiteStripGraph hN hM A K).Walk u v)
    (u' : RotatedVertex) (hproj : liftedFaceVertex hN hM hNp hMp u' = u)
    (hux : u'.val.1 = (u.val.1.val : ℤ)) :
    ∃ v' : RotatedVertex, (liftedStripGraph hNp hMp A 0 (K : ℤ)).Reachable u' v' ∧
      liftedFaceVertex hN hM hNp hMp v' = v ∧ v'.val.1 = (v.val.1.val : ℤ) := by
  induction p generalizing u' with
  | nil => exact ⟨u',SimpleGraph.Reachable.refl _,hproj,hux⟩
  | @cons u v w huv p ih =>
    obtain ⟨v',hadj,hv,hvx⟩ := finiteStrip_adj_lifts hN hM hNp hMp A K huv u' hproj hux
    obtain ⟨w',hreach,hw,hwx⟩ := ih v' hv hvx
    exact ⟨w',hadj.reachable.trans hreach,hw,hwx⟩

/-- The finite-strip crossing is an actual crossing in the integer cover (the rotated
lattice) used in `TorusRC`. -/
theorem finiteStrip_crossing_implies_lifted (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) (n : ℕ)
    (u v : FaceVertex N M true) (hu : u.val.1.val = 0) (hv : v.val.1.val = 3*n)
    (hreach : (finiteStripGraph hN hM A (3*n)).Reachable u v) :
    torusRCLeftStripCrossing hNp hMp A n := by
  obtain ⟨p⟩ := hreach
  obtain ⟨v',hr,_,hvx⟩ := finiteStrip_walk_lifts hN hM hNp hMp A (3*n) p (faceLift u)
    (faceLift_projects hN hM hNp hMp u) rfl
  exact ⟨faceLift u,v',by change (u.val.1.val : ℤ) = 0; exact_mod_cast hu,
    by rw [hvx,hv],hr⟩

end PottsDiscontinuity.TorusTopology
