/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def parafermionicCoverForward (u v : ParafermionicCoverVertex) : Prop :=
  (u.1.1 + 1 = v.1.1 ∧ u.1.2 = v.1.2) ∨
  (u.1.1 = v.1.1 ∧ u.1.2 + 1 = v.1.2)

theorem parafermionicCover_adj_forward_or_reverse {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) :
    parafermionicCoverForward u v ∨ parafermionicCoverForward v u := by
  rcases u with ⟨⟨x,y⟩,k⟩
  rcases v with ⟨⟨x',y'⟩,k'⟩
  rw [parafermionicCoverGraph_adj_iff_cases] at h
  dsimp [parafermionicCoverForward] at *
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem parafermionicCoverForward_not_reverse {u v : ParafermionicCoverVertex}
    (h₁ : parafermionicCoverForward u v) (h₂ : parafermionicCoverForward v u) : False := by
  rcases h₁ with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;>
    rcases h₂ with ⟨hx',hy'⟩ | ⟨hx',hy'⟩ <;> omega

def coverHorizontalBase (n : ℕ) : Finset LatticeVertex :=
  Finset.Ico (-(n:ℤ)) n ×ˢ Finset.Icc (-(n:ℤ)) n

def coverVerticalBase (n : ℕ) : Finset LatticeVertex :=
  Finset.Icc (-(n:ℤ)) n ×ˢ Finset.Ico (-(n:ℤ)) n

def coverSheets (n : ℕ) : Finset ℤ :=
  Finset.Icc (-((n^5:ℕ):ℤ)) ((n^5:ℕ):ℤ)

def coverHorizontalBad (n : ℕ) : Finset (LatticeVertex × ℤ) :=
  (({0} : Finset ℤ) ×ˢ Finset.Ico (-(n:ℤ)) 0) ×ˢ ({((n^5:ℕ):ℤ)} : Finset ℤ)

def coverHorizontalIndex (n : ℕ) : Finset (LatticeVertex × ℤ) :=
  (coverHorizontalBase n ×ˢ coverSheets n) \ coverHorizontalBad n

def coverVerticalIndex (n : ℕ) : Finset (LatticeVertex × ℤ) :=
  coverVerticalBase n ×ˢ coverSheets n

private theorem cover_Ico_card (n : ℕ) :
    (Finset.Ico (-(n:ℤ)) n).card = 2*n := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.card_Ico_of_le (a := -(n:ℤ)) (b := (n:ℤ)) (by omega)]
  push_cast
  ring

private theorem cover_Icc_card (n : ℕ) :
    (Finset.Icc (-(n:ℤ)) n).card = 2*n+1 := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.card_Icc_of_le (a := -(n:ℤ)) (b := (n:ℤ)) (by omega)]
  push_cast
  ring

private theorem coverHorizontalBase_card (n : ℕ) :
    (coverHorizontalBase n).card = 2*n*(2*n+1) := by
  unfold coverHorizontalBase
  rw [Finset.card_product, cover_Ico_card, cover_Icc_card]

private theorem coverVerticalBase_card (n : ℕ) :
    (coverVerticalBase n).card = (2*n+1)*2*n := by
  unfold coverVerticalBase
  rw [Finset.card_product, cover_Icc_card, cover_Ico_card]
  ring

private theorem coverSheets_card (n : ℕ) :
    (coverSheets n).card = 2*n^5+1 := by
  unfold coverSheets
  apply Nat.cast_injective (R := ℤ)
  rw [Int.card_Icc_of_le (a := -((n^5:ℕ):ℤ)) (b := ((n^5:ℕ):ℤ)) (by omega)]
  push_cast
  ring

private theorem coverHorizontalBad_card (n : ℕ) :
    (coverHorizontalBad n).card = n := by
  simp [coverHorizontalBad]

private theorem coverHorizontalBad_subset (n : ℕ) :
    coverHorizontalBad n ⊆ coverHorizontalBase n ×ˢ coverSheets n := by
  intro z hz
  rcases z with ⟨⟨x,y⟩,k⟩
  simp only [coverHorizontalBad, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico] at hz
  simp only [coverHorizontalBase, coverSheets, Finset.mem_product,
    Finset.mem_Ico, Finset.mem_Icc]
  rcases hz with ⟨⟨hx,hylo,hyhi⟩,hk⟩
  omega

private theorem coverHorizontalIndex_card (n : ℕ) :
    (coverHorizontalIndex n).card = 2*n*(2*n+1)*(2*n^5+1)-n := by
  rw [coverHorizontalIndex, Finset.card_sdiff_of_subset (coverHorizontalBad_subset n),
    Finset.card_product, coverHorizontalBase_card, coverSheets_card,
    coverHorizontalBad_card]

private theorem coverVerticalIndex_card (n : ℕ) :
    (coverVerticalIndex n).card = 2*n*(2*n+1)*(2*n^5+1) := by
  simp [coverVerticalIndex, Finset.card_product, coverVerticalBase_card, coverSheets_card]
  ring

noncomputable def coverForwardPairFinset (n : ℕ) : Finset
    (ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun p =>
    parafermionicCoverForward p.1.1 p.2.1 ∧ (parafermionicCoverBoxGraph n).Adj p.1 p.2

def coverPairEdge {n : ℕ}
    (p : ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) :
    Sym2 (ParafermionicCoverBoxVertex n) := s(p.1,p.2)

private theorem coverForwardPairFinset_image_eq_edgeFinset (n : ℕ) :
    (coverForwardPairFinset n).image coverPairEdge =
      (parafermionicCoverBoxGraph n).edgeFinset := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨p,hp,rfl⟩
    simp only [coverForwardPairFinset, Finset.mem_filter] at hp
    simpa [coverPairEdge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hp.2.2
  · intro he
    have hAdj : e ∈ (parafermionicCoverBoxGraph n).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp he
    let a := e.out.1
    let b := e.out.2
    have hout : s(a,b) = e := e.out_eq
    have hab : (parafermionicCoverBoxGraph n).Adj a b := by
      rw [← hout] at hAdj
      simpa [parafermionicCoverBoxGraph, SimpleGraph.mem_edgeSet] using hAdj
    have hbase := parafermionicCover_adj_forward_or_reverse hab
    rcases hbase with hf | hf
    · apply Finset.mem_image.mpr
      refine ⟨(a,b), ?_, ?_⟩
      · simp only [coverForwardPairFinset, Finset.mem_filter]
        exact ⟨by simp, ⟨hf, hab⟩⟩
      · exact hout
    · apply Finset.mem_image.mpr
      refine ⟨(b,a), ?_, ?_⟩
      · simp only [coverForwardPairFinset, Finset.mem_filter]
        exact ⟨by simp, ⟨hf, hab.symm⟩⟩
      · simpa [coverPairEdge, Sym2.eq_swap] using hout

private theorem coverForwardPairFinset_card_eq_edgeFinset_card (n : ℕ) :
    (coverForwardPairFinset n).card = (parafermionicCoverBoxGraph n).edgeFinset.card := by
  classical
  rw [← coverForwardPairFinset_image_eq_edgeFinset]
  symm
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  rcases p with ⟨p₁,p₂⟩
  rcases q with ⟨q₁,q₂⟩
  have hpF : parafermionicCoverForward p₁.1 p₂.1 := by
    simpa [coverForwardPairFinset] using (Finset.mem_filter.mp hp).2.1
  have hqF : parafermionicCoverForward q₁.1 q₂.1 := by
    simpa [coverForwardPairFinset] using (Finset.mem_filter.mp hq).2.1
  rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · cases h1
    cases h2
    rfl
  · cases h1
    cases h2
    exact False.elim (parafermionicCoverForward_not_reverse hpF hqF)

def coverHorizontalRawPair (z : LatticeVertex × ℤ) :
    ParafermionicCoverVertex × ParafermionicCoverVertex :=
  (((z.1, z.2)), parafermionicCoverNeighborLift ((z.1,z.2)) (z.1.1+1,z.1.2))

def coverVerticalRawPair (z : LatticeVertex × ℤ) :
    ParafermionicCoverVertex × ParafermionicCoverVertex :=
  (((z.1, z.2)), parafermionicCoverNeighborLift ((z.1,z.2)) (z.1.1,z.1.2+1))

private theorem coverHorizontalIndex_bounds (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverHorizontalIndex n) :
    -(n:ℤ) ≤ z.1.1 ∧ z.1.1 < n ∧ -(n:ℤ) ≤ z.1.2 ∧ z.1.2 ≤ n ∧
      -((n^5:ℕ):ℤ) ≤ z.2 ∧ z.2 ≤ (n^5:ℕ) ∧
      ¬ (z.1.1=0 ∧ z.1.2<0 ∧ z.2=(n^5:ℕ)) := by
  simp only [coverHorizontalIndex, coverHorizontalBase, coverSheets, coverHorizontalBad,
    Finset.mem_sdiff, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc,
    Finset.mem_singleton] at hz
  rcases hz with ⟨hgood,hbad⟩
  rcases hgood with ⟨⟨⟨hxlo,hxhi⟩,hylo,hyhi⟩,hklo,hkhi⟩
  refine ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,?_⟩
  intro ⟨hx,hy,hk⟩
  exact hbad ⟨⟨hx,by omega,hy⟩,hk⟩

private theorem coverVerticalIndex_bounds (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverVerticalIndex n) :
    -(n:ℤ) ≤ z.1.1 ∧ z.1.1 ≤ n ∧ -(n:ℤ) ≤ z.1.2 ∧ z.1.2 < n ∧
      -((n^5:ℕ):ℤ) ≤ z.2 ∧ z.2 ≤ (n^5:ℕ) := by
  simp only [coverVerticalIndex, coverVerticalBase, coverSheets, Finset.mem_product,
    Finset.mem_Ico, Finset.mem_Icc] at hz
  rcases hz with ⟨⟨⟨hxlo,hxhi⟩,hylo,hyhi⟩,⟨hklo,hkhi⟩⟩
  exact ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩

 theorem coverHorizontalRawPair_mem (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverHorizontalIndex n) :
    (coverHorizontalRawPair z).1 ∈ parafermionicCoverBoxVertices n ∧
      (coverHorizontalRawPair z).2 ∈ parafermionicCoverBoxVertices n := by
  rcases coverHorizontalIndex_bounds n z hz with
    ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hbad⟩
  have hn : 0 < n := by omega
  have hpowcast : ((n^5:ℕ):ℤ) = (n:ℤ)^5 := by norm_num
  have hp : (0:ℤ) < ((n^5:ℕ):ℤ) := by exact_mod_cast (Nat.pow_pos hn)
  have hshift : parafermionicCoverSheetShift z.1 (z.1.1+1,z.1.2) =
      if z.1.1=0 ∧ z.1.2<0 then 1 else 0 := by
    unfold parafermionicCoverSheetShift
    by_cases h : z.1.1=0 ∧ z.1.2<0 <;> simp [h]; omega
  have htlo : -((n^5:ℕ):ℤ) ≤ z.2 +
      (if z.1.1=0 ∧ z.1.2<0 then 1 else 0) := by
    by_cases h : z.1.1=0 ∧ z.1.2<0
    · simp [h]
      omega
    · simp [h]
      exact hklo
  have hthi : z.2 + (if z.1.1=0 ∧ z.1.2<0 then 1 else 0) ≤ (n^5:ℕ) := by
    by_cases h : z.1.1=0 ∧ z.1.2<0
    · have : z.2 < (n^5:ℕ) := by
        by_contra hnot
        apply hbad
        exact ⟨h.1,h.2,by omega⟩
      simp [h]
      omega
    · simp [h]
      exact hkhi
  change ((z.1,z.2) ∈ parafermionicCoverBoxVertices n) ∧
    (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1+1,z.1.2) ∈
      parafermionicCoverBoxVertices n)
  constructor
  · rw [parafermionicCoverBoxVertices_mem]
    change -(n:ℤ) ≤ z.1.1 ∧ z.1.1 ≤ n ∧ -(n:ℤ) ≤ z.1.2 ∧ z.1.2 ≤ n ∧
      -((n^5:ℕ):ℤ) ≤ z.2 ∧ z.2 ≤ (n^5:ℕ)
    exact ⟨by omega, by omega, by omega, by omega, hklo, hkhi⟩
  · rw [parafermionicCoverBoxVertices_mem]
    simp only [parafermionicCoverNeighborLift]
    rw [hshift]
    exact ⟨by omega, by omega, by omega, by omega, htlo, hthi⟩

 theorem coverVerticalRawPair_mem (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverVerticalIndex n) :
    (coverVerticalRawPair z).1 ∈ parafermionicCoverBoxVertices n ∧
      (coverVerticalRawPair z).2 ∈ parafermionicCoverBoxVertices n := by
  rcases coverVerticalIndex_bounds n z hz with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
  change ((z.1,z.2) ∈ parafermionicCoverBoxVertices n) ∧
    (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1,z.1.2+1) ∈
      parafermionicCoverBoxVertices n)
  constructor
  · rw [parafermionicCoverBoxVertices_mem]
    change -(n:ℤ) ≤ z.1.1 ∧ z.1.1 ≤ n ∧ -(n:ℤ) ≤ z.1.2 ∧ z.1.2 ≤ n ∧
      -((n^5:ℕ):ℤ) ≤ z.2 ∧ z.2 ≤ (n^5:ℕ)
    exact ⟨hxlo,hxhi,hylo,by omega,hklo,hkhi⟩
  · rw [parafermionicCoverBoxVertices_mem]
    simp only [parafermionicCoverNeighborLift]
    have hshift : parafermionicCoverSheetShift z.1 (z.1.1,z.1.2+1)=0 := by
      unfold parafermionicCoverSheetShift
      simp
    rw [hshift]
    exact ⟨hxlo,hxhi,by omega,by omega,by omega,by omega⟩

noncomputable def coverVerticalPairs (n : ℕ) : Finset
    (ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) :=
  (coverForwardPairFinset n).filter fun p => p.1.1.1.2 + 1 = p.2.1.1.2

noncomputable def verticalIndexPair (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverVerticalIndex n) :
    ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n :=
  ⟨⟨(coverVerticalRawPair z).1, (coverVerticalRawPair_mem n z hz).1⟩,
   ⟨(coverVerticalRawPair z).2, (coverVerticalRawPair_mem n z hz).2⟩⟩

private theorem verticalIndexPair_mem (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverVerticalIndex n) : verticalIndexPair n z hz ∈
      coverVerticalPairs n := by
  unfold coverVerticalPairs
  rw [Finset.mem_filter]
  constructor
  · simp only [coverForwardPairFinset, Finset.mem_filter]
    change verticalIndexPair n z hz ∈ Finset.univ ×ˢ Finset.univ ∧
      parafermionicCoverForward _ _ ∧ (parafermionicCoverBoxGraph n).Adj _ _
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_, ?_⟩
    · change parafermionicCoverForward (coverVerticalRawPair z).1
        (coverVerticalRawPair z).2
      exact Or.inr ⟨rfl, rfl⟩
    · change parafermionicCoverGraph.Adj (z.1,z.2)
        (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1,z.1.2+1))
      apply parafermionicCoverNeighborLift_adj
      rw [squareLattice_adj_iff]
      exact Or.inr ⟨rfl, Or.inl rfl⟩
  · simp [verticalIndexPair, coverVerticalRawPair, parafermionicCoverNeighborLift]

private theorem coverVerticalIndex_card_bij (n : ℕ) :
    (coverVerticalIndex n).card = (coverVerticalPairs n).card := by
  classical
  apply Finset.card_bij (fun z hz => verticalIndexPair n z hz)
  · exact verticalIndexPair_mem n
  · intro a ha b hb hab
    have h := congrArg (fun p : ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n => p.1.1) hab
    simp only [verticalIndexPair, coverVerticalRawPair] at h
    cases a with
    | mk av ak =>
      cases b with
      | mk bv bk =>
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl,rfl⟩,rfl⟩
        rfl
  · intro p hp
    simp only [coverVerticalPairs, Finset.mem_filter] at hp
    rcases hp with ⟨hp,hy⟩
    have hparts : parafermionicCoverForward p.1.1 p.2.1 ∧
        (parafermionicCoverBoxGraph n).Adj p.1 p.2 := by
      simpa [coverForwardPairFinset] using hp
    have hbase : p.2.1.1.1 = p.1.1.1.1 ∧ p.2.1.1.2 = p.1.1.1.2+1 := by
      rcases hparts.1 with hh | hv
      · have : False := by omega
        exact False.elim this
      · exact ⟨hv.1.symm, hv.2.symm⟩
    have hadj : parafermionicCoverGraph.Adj p.1.1 p.2.1 := hparts.2
    have hsecond : p.2.1 = parafermionicCoverNeighborLift p.1.1
        (p.1.1.1.1,p.1.1.1.2+1) := by
      apply parafermionicCoverNeighborLift_unique
      · exact Prod.ext hbase.1 hbase.2
      · exact hadj
    let z : LatticeVertex × ℤ := ((p.1.1.1.1,p.1.1.1.2),p.1.1.2)
    have hz : z ∈ coverVerticalIndex n := by
      simp only [coverVerticalIndex, coverVerticalBase, coverSheets, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Ico]
      rcases (parafermionicCoverBoxVertices_mem n p.1.1).mp p.1.2 with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
      rcases (parafermionicCoverBoxVertices_mem n p.2.1).mp p.2.2 with ⟨_,_,_,hyhi2,_,_⟩
      dsimp [z]
      exact ⟨⟨⟨hxlo,hxhi⟩,hylo,by omega⟩,hklo,hkhi⟩
    refine ⟨z,hz,?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [verticalIndexPair, coverVerticalRawPair, z]
    · apply Subtype.ext
      simp [verticalIndexPair, coverVerticalRawPair, z, hsecond]

noncomputable def coverHorizontalPairs (n : ℕ) : Finset
    (ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n) :=
  (coverForwardPairFinset n).filter fun p => p.1.1.1.1 + 1 = p.2.1.1.1

noncomputable def horizontalIndexPair (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverHorizontalIndex n) :
    ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n :=
  ⟨⟨(coverHorizontalRawPair z).1, (coverHorizontalRawPair_mem n z hz).1⟩,
   ⟨(coverHorizontalRawPair z).2, (coverHorizontalRawPair_mem n z hz).2⟩⟩

private theorem horizontalIndexPair_mem (n : ℕ) (z : LatticeVertex × ℤ)
    (hz : z ∈ coverHorizontalIndex n) : horizontalIndexPair n z hz ∈
      coverHorizontalPairs n := by
  unfold coverHorizontalPairs
  rw [Finset.mem_filter]
  constructor
  · simp only [coverForwardPairFinset, Finset.mem_filter]
    change horizontalIndexPair n z hz ∈ Finset.univ ×ˢ Finset.univ ∧
      parafermionicCoverForward _ _ ∧
      (parafermionicCoverBoxGraph n).Adj _ _
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_, ?_⟩
    · change parafermionicCoverForward ((z.1,z.2))
        (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1+1,z.1.2))
      exact Or.inl ⟨rfl,rfl⟩
    · change parafermionicCoverGraph.Adj (z.1,z.2)
        (parafermionicCoverNeighborLift (z.1,z.2) (z.1.1+1,z.1.2))
      apply parafermionicCoverNeighborLift_adj
      rw [squareLattice_adj_iff]
      exact Or.inl ⟨Or.inl rfl,rfl⟩
  · simp [horizontalIndexPair, coverHorizontalRawPair,
      parafermionicCoverNeighborLift]

private theorem coverHorizontalIndex_card_bij (n : ℕ) :
    (coverHorizontalIndex n).card = (coverHorizontalPairs n).card := by
  classical
  apply Finset.card_bij (fun z hz => horizontalIndexPair n z hz)
  · exact horizontalIndexPair_mem n
  · intro a ha b hb hab
    have h := congrArg (fun p : ParafermionicCoverBoxVertex n × ParafermionicCoverBoxVertex n => p.1.1) hab
    simp only [horizontalIndexPair, coverHorizontalRawPair] at h
    cases a with
    | mk av ak =>
      cases b with
      | mk bv bk =>
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl,rfl⟩,rfl⟩
        rfl
  · intro p hp
    simp only [coverHorizontalPairs, Finset.mem_filter] at hp
    rcases hp with ⟨hp,hx⟩
    have hparts :
        parafermionicCoverForward p.1.1 p.2.1 ∧
        (parafermionicCoverBoxGraph n).Adj p.1 p.2 := by
      simpa [coverForwardPairFinset] using hp
    have hbase : p.2.1.1.1 = p.1.1.1.1+1 ∧ p.2.1.1.2 = p.1.1.1.2 := by
      rcases hparts.1 with hh | hv
      · exact ⟨hh.1.symm, hh.2.symm⟩
      · have hfalse : False := by omega
        exact False.elim hfalse
    have hadj : parafermionicCoverGraph.Adj p.1.1 p.2.1 := hparts.2
    have hshift := parafermionicCover_sheetShift_of_adj hadj
    have hsecond : p.2.1 = parafermionicCoverNeighborLift p.1.1
        (p.1.1.1.1+1,p.1.1.1.2) := by
      apply parafermionicCoverNeighborLift_unique
      · exact Prod.ext hbase.1 hbase.2
      · exact hadj
    let z : LatticeVertex × ℤ := ((p.1.1.1.1,p.1.1.1.2),p.1.1.2)
    have hz : z ∈ coverHorizontalIndex n := by
      simp only [coverHorizontalIndex, Finset.mem_sdiff, Finset.mem_product,
        coverHorizontalBase, coverSheets, Finset.mem_Ico, Finset.mem_Icc,
        coverHorizontalBad, Finset.mem_singleton]
      rcases (parafermionicCoverBoxVertices_mem n p.1.1).mp p.1.2 with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
      rcases (parafermionicCoverBoxVertices_mem n p.2.1).mp p.2.2 with ⟨_,hxhi2,_,_,_,hkhi2⟩
      dsimp [z]
      refine ⟨?_,?_⟩
      · exact ⟨⟨⟨hxlo,by omega⟩,hylo,hyhi⟩,hklo,hkhi⟩
      · intro hbad
        have hs : parafermionicCoverSheetShift (p.1.1.1) (p.2.1.1) = 1 := by
          unfold parafermionicCoverSheetShift
          simp [hbase.1, hbase.2, hbad.1.1, hbad.1.2.2]
        rw [hs] at hshift
        rw [hbad.2] at hshift
        norm_cast at hshift hkhi2
        omega
    refine ⟨z, hz, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [horizontalIndexPair, coverHorizontalRawPair, z]
    · apply Subtype.ext
      simp [horizontalIndexPair, coverHorizontalRawPair, z, hsecond]

private theorem coverForwardPairFinset_eq_union (n : ℕ) :
    coverForwardPairFinset n = coverHorizontalPairs n ∪ coverVerticalPairs n := by
  classical
  ext p
  simp only [coverHorizontalPairs, coverVerticalPairs, Finset.mem_union,
    Finset.mem_filter, coverForwardPairFinset]
  constructor
  · rintro ⟨_,hf,ha⟩
    rcases hf with hh | hv
    · left
      exact ⟨⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        Or.inl hh,ha⟩, by omega⟩
    · right
      exact ⟨⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        Or.inr hv,ha⟩, by omega⟩
  · rintro (⟨⟨_,hf,ha⟩,hx⟩ | ⟨⟨_,hf,ha⟩,hy⟩)
    · exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,hf,ha⟩
    · exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,hf,ha⟩

private theorem coverHorizontalVertical_disjoint (n : ℕ) :
    Disjoint (coverHorizontalPairs n) (coverVerticalPairs n) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  simp only [coverHorizontalPairs, coverVerticalPairs, Finset.mem_filter] at hp hq
  rcases hp with ⟨hp,hx⟩
  rcases hq with ⟨hq,hy⟩
  have hforward : parafermionicCoverForward p.1.1 p.2.1 ∧
      (parafermionicCoverBoxGraph n).Adj p.1 p.2 := by
    simpa [coverForwardPairFinset] using hp
  rcases hforward.1 with hh | hv <;> omega

 theorem parafermionicCoverBoxGraph_edgeFinset_card_add_n (n : ℕ) (hn : 0 < n) :
    (parafermionicCoverBoxGraph n).edgeFinset.card + n =
      4*n*(2*n+1)*(2*n^5+1) := by
  have hpair := coverForwardPairFinset_card_eq_edgeFinset_card n
  rw [← hpair, coverForwardPairFinset_eq_union,
    Finset.card_union_of_disjoint (coverHorizontalVertical_disjoint n),
    ← coverHorizontalIndex_card_bij, ← coverVerticalIndex_card_bij,
    coverHorizontalIndex_card, coverVerticalIndex_card]
  have hbase : n ≤ 2*n*(2*n+1)*(2*n^5+1) := by
    have hn1 : 1 ≤ n := by omega
    have ha : 1 ≤ 2*n+1 := by omega
    have hb : 1 ≤ 2*n^5+1 := by omega
    have hmul : 0 < (2*n+1)*(2*n^5+1) := Nat.mul_pos (by omega) (by omega)
    have hfactor : 1 ≤ 2*((2*n+1)*(2*n^5+1)) := by omega
    have hmuln := Nat.mul_le_mul_left n hfactor
    nlinarith
  have hsum : 2*n*(2*n+1)*(2*n^5+1)-n +
      2*n*(2*n+1)*(2*n^5+1) + n =
      2*(2*n*(2*n+1)*(2*n^5+1)) := by omega
  rw [hsum]
  ring

end PottsDiscontinuity.TorusTopology.Planar.Medial
