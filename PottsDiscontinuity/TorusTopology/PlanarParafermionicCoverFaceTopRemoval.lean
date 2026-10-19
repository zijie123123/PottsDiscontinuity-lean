/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverBoxConnectivity
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceTopEdges

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The actual finite cover graph after deleting every retained ordinary face's
positively oriented top edge. -/
def parafermionicCoverBoxGraphWithoutFaceTops (n : ℕ) :
    SimpleGraph (ParafermionicCoverBoxVertex n) where
  Adj u v := (parafermionicCoverBoxGraph n).Adj u v ∧
    ∀ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge f ≠ s(u.1,v.1)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    intro f hf heq
    apply h.2 f hf
    calc
      parafermionicCoverFiniteFaceTopEdge f = s(v.1,u.1) := heq
      _ = s(u.1,v.1) := Sym2.eq_swap⟩
  loopless := ⟨by
    intro u h
    exact (parafermionicCoverBoxGraph n).loopless.irrefl u h.1⟩

private theorem parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top
    (n : ℕ) {u v : ParafermionicCoverBoxVertex n}
    (h : (parafermionicCoverBoxGraph n).Adj u v)
    (hnot : ∀ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge f ≠ s(u.1,v.1)) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj u v := ⟨h,hnot⟩

private theorem topEdge_ne_of_same_base_x
    {u v : ParafermionicCoverVertex}
    (hux : u.1.1 = v.1.1) (f : ParafermionicCoverVertex) :
    parafermionicCoverFiniteFaceTopEdge f ≠ s(u,v) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hx1 := congrArg (fun z : ParafermionicCoverVertex => z.1.1) h1
    have hx2 := congrArg (fun z : ParafermionicCoverVertex => z.1.1) h2
    simp [parafermionicCoverFaceRightUpLift_formula,
      parafermionicCoverFaceRightUpLeftLift_formula] at hx1 hx2
    omega
  · have hx1 := congrArg (fun z : ParafermionicCoverVertex => z.1.1) h1
    have hx2 := congrArg (fun z : ParafermionicCoverVertex => z.1.1) h2
    simp [parafermionicCoverFaceRightUpLift_formula,
      parafermionicCoverFaceRightUpLeftLift_formula] at hx1 hx2
    omega

theorem parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x
    (n : ℕ) {u v : ParafermionicCoverBoxVertex n}
    (h : (parafermionicCoverBoxGraph n).Adj u v)
    (hux : u.1.1.1 = v.1.1.1) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj u v := by
  apply parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top n h
  intro f hf he
  exact topEdge_ne_of_same_base_x hux f he

def coverFacePoint (n : ℕ) (v : ParafermionicCoverVertex)
    (hv : v ∈ parafermionicCoverBoxVertices n) : ParafermionicCoverBoxVertex n :=
  ⟨v,hv⟩

 theorem coverFace_bottom_endpoints_mem (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    f ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2 ∈ parafermionicCoverBoxVertices n :=
  parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
    (e := Prod.mk f (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
    (by simp [parafermionicCoverFiniteFaceDarts])

def coverFaceS (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  coverFacePoint n f (coverFace_bottom_endpoints_mem n f hf).1

def coverFaceR (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  coverFacePoint n (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)
    (coverFace_bottom_endpoints_mem n f hf).2

def coverFaceU (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  coverFacePoint n (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1

def coverFaceL (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  coverFacePoint n (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2

private theorem coverFace_bottom_adj_of_not_removed (n : ℕ)
    (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hnot : ∀ g ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge g ≠
        s(f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj (coverFaceS n f hf)
      (coverFaceR n f hf) := by
  apply parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top n
  · change parafermionicCoverGraph.Adj f
      (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)
    have hmem : Prod.mk f (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2) ∈
        parafermionicCoverFiniteFaceDarts f := by
      simp [parafermionicCoverFiniteFaceDarts]
    exact parafermionicCoverFiniteFaceDart_adjacent n f hf hmem
  · intro g hg he
    exact hnot g hg he

private theorem cover_int_toNat_lt {a b : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) : a.toNat < b.toNat := by
  omega

private theorem coverFace_top_reachable (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable
      (coverFaceU n f hf) (coverFaceL n f hf) := by
  let rank (g : ParafermionicCoverVertex) := (g.1.2 + (n : ℤ)).toNat
  have H : ∀ m (g : ParafermionicCoverVertex) (hrank : rank g ≤ m)
      (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n),
      (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable
        (coverFaceU n g hg) (coverFaceL n g hg) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g hrank hg
      have hcrit := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n g).mp hg
      rcases g with ⟨⟨x,y⟩,k⟩
      have hnot : (x,y) ≠ (0,-1) := by
        rcases hcrit with ⟨_,_,_,_,_,_,hnot,_⟩
        exact hnot
      let U := coverFaceU n ((x,y),k) hg
      let L := coverFaceL n ((x,y),k) hg
      let R := coverFaceR n ((x,y),k) hg
      let S := coverFaceS n ((x,y),k) hg
      have hU_R : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable U R := by
        have hadj : (parafermionicCoverBoxGraph n).Adj R U := by
          change parafermionicCoverGraph.Adj
            (parafermionicCoverFaceRightLift x y k)
            (parafermionicCoverFaceRightUpLift x y k)
          have hm : Prod.mk (parafermionicCoverFaceRightLift x y k)
              (parafermionicCoverFaceRightUpLift x y k) ∈
              parafermionicCoverFiniteFaceDarts ((x,y),k) := by
            simp [parafermionicCoverFiniteFaceDarts]
          exact parafermionicCoverFiniteFaceDart_adjacent n ((x,y),k) hg hm
        have hx : R.1.1.1 = U.1.1.1 := by rfl
        exact (parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x n hadj hx).symm.reachable
      have hS_L : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable S L := by
        have hadj : (parafermionicCoverBoxGraph n).Adj L S := by
          change parafermionicCoverGraph.Adj
            (parafermionicCoverFaceRightUpLeftLift x y k) ((x,y),k)
          have hm : Prod.mk (parafermionicCoverFaceRightUpLeftLift x y k) ((x,y),k) ∈
              parafermionicCoverFiniteFaceDarts ((x,y),k) := by
            simp [parafermionicCoverFiniteFaceDarts]
          exact parafermionicCoverFiniteFaceDart_adjacent n ((x,y),k) hg hm
        have hx : L.1.1.1 = S.1.1.1 := by rfl
        exact (parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x n hadj hx).symm.reachable
      by_cases hremoved : ∃ g' ∈ parafermionicCoverFiniteOrdinaryFaces n,
          parafermionicCoverFiniteFaceTopEdge g' = s(((x,y),k),
            parafermionicCoverFaceRightLift x y k)
      · obtain ⟨g',hg',hedge⟩ := hremoved
        have hlow : g'.1.2 < y := by
          by_contra h
          have hle : y ≤ g'.1.2 := by omega
          exact (parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le hg hg' hle)
            (by simpa [parafermionicCoverFiniteFaceBottomEdge] using hedge.symm)
        have hnonneg : 0 ≤ y + (n : ℤ) := by
          have hc := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hg
          have hylo : -(n : ℤ) ≤ y := by
            rcases hc with ⟨_,_,hylo,_,_,_,_,_⟩
            exact hylo
          omega
        have hgNonneg : 0 ≤ g'.1.2 + (n : ℤ) := by
          have hc := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n g').mp hg'
          omega
        have hrankLower : rank g' < rank ((x,y),k) := by
          dsimp [rank]
          exact cover_int_toNat_lt hgNonneg hnonneg (by omega)
        have hlt : rank g' < m := lt_of_lt_of_le hrankLower hrank
        have hreachg := ih (rank g') hlt g' (Nat.le_refl _) hg'
        have hbridge : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable R S := by
          rcases Sym2.eq_iff.mp hedge with ⟨hU,hL⟩ | ⟨hU,hL⟩
          · have hU' : coverFaceU n g' hg' = S := by
              apply Subtype.ext
              change parafermionicCoverFaceRightUpLift g'.1.1 g'.1.2 g'.2 = ((x,y),k)
              exact hU
            have hL' : coverFaceL n g' hg' = R := by
              apply Subtype.ext
              change parafermionicCoverFaceRightUpLeftLift g'.1.1 g'.1.2 g'.2 =
                parafermionicCoverFaceRightLift x y k
              exact hL
            simpa [U,L,R,S,hU',hL'] using hreachg.symm
          · have hU' : coverFaceU n g' hg' = R := by
              apply Subtype.ext
              change parafermionicCoverFaceRightUpLift g'.1.1 g'.1.2 g'.2 =
                parafermionicCoverFaceRightLift x y k
              exact hU
            have hL' : coverFaceL n g' hg' = S := by
              apply Subtype.ext
              change parafermionicCoverFaceRightUpLeftLift g'.1.1 g'.1.2 g'.2 = ((x,y),k)
              exact hL
            simpa [U,L,R,S,hU',hL'] using hreachg
        exact hU_R.trans (hbridge.trans hS_L)
      · have hbottom : (parafermionicCoverBoxGraphWithoutFaceTops n).Adj S R :=
          coverFace_bottom_adj_of_not_removed n ((x,y),k) hg (by
            intro g' hg' he
            exact hremoved ⟨g',hg',he⟩)
        exact hU_R.trans (hbottom.symm.reachable.trans hS_L)
  exact H (rank f) f le_rfl hf

theorem parafermionicCoverBoxGraphWithoutFaceTops_connected
    (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Connected := by
  have hnZ : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
  have hn5Z : 0 ≤ ((n^5 : ℕ) : ℤ) := Int.natCast_nonneg _
  have horigin : (((0:ℤ),(0:ℤ)),(0:ℤ)) ∈ parafermionicCoverBoxVertices n := by
    rw [parafermionicCoverBoxVertices_mem]
    norm_num
  let v : ParafermionicCoverBoxVertex n := ⟨((0,0),0), horigin⟩
  let : Nonempty (ParafermionicCoverBoxVertex n) := ⟨v⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨w⟩ := parafermionicCoverBoxGraph_connected n hn u v
  induction w with
  | nil => exact .rfl
  | @cons a b c hab w ih =>
      have hstep : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable a b := by
        by_cases htop : ∃ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
            parafermionicCoverFiniteFaceTopEdge f = s(a.1,b.1)
        · obtain ⟨f,hf,he⟩ := htop
          rcases Sym2.eq_iff.mp he with ⟨hU,hL⟩ | ⟨hU,hL⟩
          · have hU' : coverFaceU n f hf = a := by
              apply Subtype.ext
              exact hU
            have hL' : coverFaceL n f hf = b := by
              apply Subtype.ext
              exact hL
            simpa [hU',hL'] using coverFace_top_reachable n f hf
          · have hU' : coverFaceU n f hf = b := by
              apply Subtype.ext
              exact hU
            have hL' : coverFaceL n f hf = a := by
              apply Subtype.ext
              exact hL
            simpa [hU',hL'] using (coverFace_top_reachable n f hf).symm
        · have hadj : (parafermionicCoverBoxGraphWithoutFaceTops n).Adj a b :=
            parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top n hab (by
              intro f hf he
              exact htop ⟨f,hf,he⟩)
          exact hadj.reachable
      exact hstep.trans ih

end PottsDiscontinuity.TorusTopology.Planar.Medial
