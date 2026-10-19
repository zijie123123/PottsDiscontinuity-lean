/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaceIncidence

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The actual upper edge of the positively oriented lifted face, as an
unordered edge of the ambient cover graph. -/
def parafermionicCoverFiniteFaceTopEdge (f : ParafermionicCoverVertex) :
    Sym2 ParafermionicCoverVertex :=
  s(parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
    parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)

theorem parafermionicCoverFiniteFaceTopEdge_endpoints_mem
    (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2) ∈ parafermionicCoverBoxVertices n ∧
    (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2) ∈
      parafermionicCoverBoxVertices n := by
  exact parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
    (e := Prod.mk (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)) (by simp [parafermionicCoverFiniteFaceDarts])

theorem parafermionicCoverFiniteFaceTopEdge_adjacent
    (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (parafermionicCoverBoxGraph n).Adj
      ⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩
      ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩ := by
  change parafermionicCoverGraph.Adj
    (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
    (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)
  exact parafermionicCoverFiniteFaceDart_adjacent n f hf
    (e := Prod.mk (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)) (by simp [parafermionicCoverFiniteFaceDarts])


theorem parafermionicCoverFiniteFaceTopEdge_mem_edgeSet
    (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    s(⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩,
      ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩) ∈
      (parafermionicCoverBoxGraph n).edgeSet := by
  simpa [SimpleGraph.mem_edgeSet] using
    parafermionicCoverFiniteFaceTopEdge_adjacent n f hf


private theorem coverFaceLeftLift_of_not_branch (x y k : ℤ)
    (h : (x,y) ≠ (0,-1)) :
    parafermionicCoverFaceRightUpLeftLift x y k = ((x,y+1),k) := by
  rw [parafermionicCoverFaceRightUpLeftLift_formula]
  by_cases hx : x = 0
  · by_cases hy : y < 0
    · have hylt : y < -1 := by
        by_contra hh
        have : y = -1 := by omega
        exact h (Prod.ext hx this)
      have hy' : y+1 < 0 := by omega
      simp [hx,hy,hy']
    · simp [hx,hy]
      omega
  · simp [hx]

theorem parafermionicCoverFiniteFaceTopEdge_injective (n : ℕ)
    {f g : ParafermionicCoverVertex}
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (he : parafermionicCoverFiniteFaceTopEdge f =
      parafermionicCoverFiniteFaceTopEdge g) : f = g := by
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  simp only [parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightUpLift_formula, Sym2.eq_iff] at he
  rcases he with ⟨hu,hl⟩ | ⟨hu,hl⟩
  · have hbase := congrArg (fun z : ParafermionicCoverVertex => z.1) hu
    have hxx : x = x' := by
      have hh := congrArg Prod.fst hbase
      simp at hh
      omega
    have hyy : y = y' := by
      have hh := congrArg Prod.snd hbase
      simp at hh
      omega
    have hs := congrArg (fun z : ParafermionicCoverVertex => z.2) hu
    simp at hs
    simp only [Prod.mk.injEq]
    exact ⟨⟨hxx,hyy⟩,by omega⟩
  · have hbase := congrArg (fun z : ParafermionicCoverVertex => z.1) hu
    have hx1 := congrArg Prod.fst hbase
    have hx2 := congrArg Prod.fst (congrArg (fun z : ParafermionicCoverVertex => z.1) hl)
    simp at hx1 hx2
    omega


def parafermionicCoverFiniteFaceBottomEdge (f : ParafermionicCoverVertex) :
    Sym2 ParafermionicCoverVertex :=
  s(f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)

def parafermionicCoverFiniteFaceRightEdge (f : ParafermionicCoverVertex) :
    Sym2 ParafermionicCoverVertex :=
  s(parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
    parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)

def parafermionicCoverFiniteFaceLeftEdge (f : ParafermionicCoverVertex) :
    Sym2 ParafermionicCoverVertex :=
  s(parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f)

theorem parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le
    {n : ℕ} {f g : ParafermionicCoverVertex}
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hheight : f.1.2 ≤ g.1.2) :
    parafermionicCoverFiniteFaceBottomEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  have hcf := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hf
  have hcg := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x',y'),k')).mp hg
  rcases hcg with ⟨_,_,_,_,_,_,hnot',_⟩
  have hleft' := coverFaceLeftLift_of_not_branch x' y' k' hnot'
  intro he
  simp only [parafermionicCoverFiniteFaceBottomEdge,
    parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula, hleft', Sym2.eq_iff] at he
  rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hb := congrArg (fun z : ParafermionicCoverVertex => z.1) h1
    have hb' := congrArg (fun z : ParafermionicCoverVertex => z.1) h2
    simp at hb hb'
    have : x = x' + 1 := by omega
    omega
  · have hb := congrArg (fun z : ParafermionicCoverVertex => z.1) h1
    have hb' := congrArg (fun z : ParafermionicCoverVertex => z.1) h2
    simp at hb hb'
    rcases hb with ⟨_,hy⟩
    change y ≤ y' at hheight
    omega



theorem parafermionicCoverFiniteFaceRightEdge_ne_topEdge
    {n : ℕ} {f g : ParafermionicCoverVertex}
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    parafermionicCoverFiniteFaceRightEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  have hcg := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x',y'),k')).mp hg
  rcases hcg with ⟨_,_,_,_,_,_,hnot',_⟩
  have hleft' := coverFaceLeftLift_of_not_branch x' y' k' hnot'
  intro he
  simp only [parafermionicCoverFiniteFaceRightEdge,
    parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula, hleft', Sym2.eq_iff] at he
  rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hb1 := congrArg (fun z : ParafermionicCoverVertex => z.1) h1
    have hb2 := congrArg (fun z : ParafermionicCoverVertex => z.1) h2
    simp at hb1 hb2
    rcases hb1 with ⟨hx,hy⟩
    rcases hb2 with ⟨hx',hy'⟩
    omega
  · have hb1 := congrArg (fun z : ParafermionicCoverVertex => z.1) h1
    have hb2 := congrArg (fun z : ParafermionicCoverVertex => z.1) h2
    simp at hb1 hb2
    rcases hb1 with ⟨hx,hy⟩
    rcases hb2 with ⟨hx',hy'⟩
    omega

theorem parafermionicCoverFiniteFaceLeftEdge_ne_topEdge
    {n : ℕ} {f g : ParafermionicCoverVertex}
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    parafermionicCoverFiniteFaceLeftEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  have hcf := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hf
  have hcg := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x',y'),k')).mp hg
  rcases hcf with ⟨_,_,_,_,_,_,hnot,_⟩
  rcases hcg with ⟨_,_,_,_,_,_,hnot',_⟩
  have hleft := coverFaceLeftLift_of_not_branch x y k hnot
  have hleft' := coverFaceLeftLift_of_not_branch x' y' k' hnot'
  intro he
  simp only [parafermionicCoverFiniteFaceLeftEdge,
    parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightUpLift_formula,
    hleft,hleft', Sym2.eq_iff] at he
  rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hb1 := congrArg (fun z : ParafermionicCoverVertex => z.1) h1
    have hb2 := congrArg (fun z : ParafermionicCoverVertex => z.1) h2
    simp at hb1 hb2
    rcases hb1 with ⟨hx,hy⟩
    rcases hb2 with ⟨hx',hy'⟩
    omega
  · have hb1 := congrArg (fun z : ParafermionicCoverVertex => z.1) h1
    have hb2 := congrArg (fun z : ParafermionicCoverVertex => z.1) h2
    simp at hb1 hb2
    rcases hb1 with ⟨hx,hy⟩
    rcases hb2 with ⟨hx',hy'⟩
    omega


end PottsDiscontinuity.TorusTopology.Planar.Medial
