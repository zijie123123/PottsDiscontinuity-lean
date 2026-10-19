/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceTopTree

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

abbrev ParafermionicCoverFiniteFaceTopIndex (n : ℕ) :=
  {f : ParafermionicCoverVertex // f ∈ parafermionicCoverFiniteOrdinaryFaces n}

/-- The retained face's actual positively oriented top edge, carried by the
finite box vertex type. -/
def parafermionicCoverFiniteFaceTopPivot (n : ℕ)
    (f : ParafermionicCoverFiniteFaceTopIndex n) :
    Sym2 (ParafermionicCoverBoxVertex n) :=
  s(⟨parafermionicCoverFaceRightUpLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).1⟩,
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).2⟩)

theorem parafermionicCoverFiniteFaceTopPivot_map (n : ℕ)
    (f : ParafermionicCoverFiniteFaceTopIndex n) :
    Sym2.map Subtype.val (parafermionicCoverFiniteFaceTopPivot n f) =
      parafermionicCoverFiniteFaceTopEdge f.1 := by
  simp [parafermionicCoverFiniteFaceTopPivot, parafermionicCoverFiniteFaceTopEdge,
    Sym2.map_mk]

theorem parafermionicCoverFiniteFaceTopPivot_injective (n : ℕ) :
    Function.Injective (parafermionicCoverFiniteFaceTopPivot n) := by
  intro f g h
  apply Subtype.ext
  apply parafermionicCoverFiniteFaceTopEdge_injective n f.2 g.2
  have hm := congrArg (Sym2.map Subtype.val) h
  rw [parafermionicCoverFiniteFaceTopPivot_map,
    parafermionicCoverFiniteFaceTopPivot_map] at hm
  exact hm

theorem parafermionicCoverFiniteFaceTopPivot_mem_edgeSet (n : ℕ)
    (f : ParafermionicCoverFiniteFaceTopIndex n) :
    parafermionicCoverFiniteFaceTopPivot n f ∈
      (parafermionicCoverBoxGraph n).edgeSet := by
  change (parafermionicCoverBoxGraph n).Adj
    ⟨parafermionicCoverFaceRightUpLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).1⟩
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).2⟩
  simpa only [SimpleGraph.mem_edgeSet] using
    parafermionicCoverFiniteFaceTopEdge_adjacent n f.1 f.2

def parafermionicCoverFiniteFaceTopRank (n : ℕ)
    (f : ParafermionicCoverFiniteFaceTopIndex n) : ℕ :=
  (f.1.1.2 + (n : ℤ)).toNat

theorem parafermionicCoverFiniteFaceTopRank_strict_height (n : ℕ)
    {f g : ParafermionicCoverFiniteFaceTopIndex n}
    (hheight : f.1.1.2 < g.1.1.2) :
    parafermionicCoverFiniteFaceTopRank n f <
      parafermionicCoverFiniteFaceTopRank n g := by
  have hf := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n f.1).mp f.2
  have hg := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n g.1).mp g.2
  rcases hf with ⟨_,_,hflo,_,_,_,_,_⟩
  rcases hg with ⟨_,_,hglow,_,_,_,_,_⟩
  unfold parafermionicCoverFiniteFaceTopRank
  have hfcast : ((f.1.1.2 + (n : ℤ)).toNat : ℤ) = f.1.1.2 + (n : ℤ) :=
    Int.toNat_of_nonneg (by omega)
  have hgcast : ((g.1.1.2 + (n : ℤ)).toNat : ℤ) = g.1.1.2 + (n : ℤ) :=
    Int.toNat_of_nonneg (by omega)
  have hnat : ((f.1.1.2 + (n : ℤ)).toNat : ℤ) <
      ((g.1.1.2 + (n : ℤ)).toNat : ℤ) := by
    rw [hfcast, hgcast]
    omega
  exact_mod_cast hnat

theorem parafermionicCoverBoxGraph_deleteTopPivots_eq (n : ℕ) :
    (parafermionicCoverBoxGraph n).deleteEdges
      (Set.range (parafermionicCoverFiniteFaceTopPivot n)) =
        parafermionicCoverBoxGraphWithoutFaceTops n := by
  ext u v
  rw [SimpleGraph.deleteEdges_adj]
  change ((parafermionicCoverBoxGraph n).Adj u v ∧
      s(u,v) ∉ Set.range (parafermionicCoverFiniteFaceTopPivot n)) ↔
    ((parafermionicCoverBoxGraph n).Adj u v ∧
      ∀ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
        parafermionicCoverFiniteFaceTopEdge f ≠ s(u.1,v.1))
  constructor
  · rintro ⟨hadj,hnot⟩
    refine ⟨hadj,?_⟩
    intro f hf htop
    let f' : ParafermionicCoverFiniteFaceTopIndex n := ⟨f,hf⟩
    have hmap : Sym2.map Subtype.val (parafermionicCoverFiniteFaceTopPivot n f') =
        Sym2.map Subtype.val (s(u,v)) := by
      rw [parafermionicCoverFiniteFaceTopPivot_map]
      simpa using htop
    have heq : parafermionicCoverFiniteFaceTopPivot n f' = s(u,v) :=
      Sym2.map.injective Subtype.val_injective hmap
    exact hnot (Set.mem_range.mpr ⟨f',heq⟩)
  · rintro ⟨hadj,hnot⟩
    refine ⟨hadj,?_⟩
    intro hmem
    obtain ⟨f,heq⟩ := Set.mem_range.mp hmem
    apply hnot f.1 f.2
    have hmap := congrArg (Sym2.map Subtype.val) heq
    rw [parafermionicCoverFiniteFaceTopPivot_map] at hmap
    simpa using hmap

theorem parafermionicCoverBoxGraph_deleteTopPivots_isAcyclic
    (n : ℕ) (hn : 1 ≤ n) :
    ((parafermionicCoverBoxGraph n).deleteEdges
      (Set.range (parafermionicCoverFiniteFaceTopPivot n))).IsAcyclic := by
  rw [parafermionicCoverBoxGraph_deleteTopPivots_eq]
  exact (parafermionicCoverBoxGraphWithoutFaceTops_isTree n hn).isAcyclic

end PottsDiscontinuity.TorusTopology.Planar.Medial
