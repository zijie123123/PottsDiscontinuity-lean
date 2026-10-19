/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def faceBaseRange (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) ((n : ℤ) - 1)
def faceSheetRange (n : ℕ) : Finset ℤ :=
  Finset.Icc (-((n ^ 5 : ℕ) : ℤ)) ((n ^ 5 : ℕ) : ℤ)
def faceFullCarrier (n : ℕ) : Finset ParafermionicCoverVertex :=
  ((faceBaseRange n ×ˢ faceBaseRange n) ×ˢ faceSheetRange n)
def faceBranchFiber (n : ℕ) : Finset ParafermionicCoverVertex :=
  ({(0,-1)} : Finset (ℤ × ℤ)) ×ˢ faceSheetRange n
def faceSeamTopFiber (n : ℕ) : Finset ParafermionicCoverVertex :=
  (({0} : Finset ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (-2)) ×ˢ
    ({((n ^ 5 : ℕ) : ℤ)} : Finset ℤ)

private theorem faceBaseRange_card (n : ℕ) :
    (faceBaseRange n).card = 2*n := by
  have h : ((faceBaseRange n).card : ℤ) = 2*(n : ℤ) := by
    change ((Finset.Icc (-(n : ℤ)) ((n : ℤ)-1)).card : ℤ) = _
    calc
      _ = ((n : ℤ)-1) + 1 - (-(n : ℤ)) :=
        Int.card_Icc_of_le (-(n : ℤ)) ((n : ℤ)-1) (by omega)
      _ = 2*(n : ℤ) := by ring
  exact_mod_cast h

private theorem faceSheetRange_card (n : ℕ) :
    (faceSheetRange n).card = 2*n^5+1 := by
  have h : ((faceSheetRange n).card : ℤ) =
      2*((n^5 : ℕ) : ℤ)+1 := by
    change ((Finset.Icc (-((n^5:ℕ):ℤ)) ((n^5:ℕ):ℤ)).card : ℤ) = _
    calc
      _ = ((n^5:ℕ):ℤ) + 1 - (-((n^5:ℕ):ℤ)) :=
        Int.card_Icc_of_le (-((n^5:ℕ):ℤ)) ((n^5:ℕ):ℤ) (by omega)
      _ = 2*((n^5:ℕ):ℤ)+1 := by ring
  exact_mod_cast h

private theorem faceFullCarrier_card (n : ℕ) :
    (faceFullCarrier n).card = (2*n)^2 * (2*n^5+1) := by
  simp [faceFullCarrier, faceBaseRange_card, faceSheetRange_card, Finset.card_product]
  ring

private theorem faceBranchFiber_card (n : ℕ) :
    (faceBranchFiber n).card = 2*n^5+1 := by
  simp [faceBranchFiber, faceSheetRange_card]

private theorem faceSeamTopFiber_card (n : ℕ) (hn : 1 ≤ n) :
  (faceSeamTopFiber n).card = n-1 := by
  have hcard : ((Finset.Icc (-(n : ℤ)) (-2)).card : ℤ) = n-1 := by
    calc
      _ = -2 + 1 - (-(n : ℤ)) :=
        Int.card_Icc_of_le (-(n : ℤ)) (-2) (by omega)
      _ = (n : ℤ)-1 := by ring
  have hnat : (Finset.Icc (-(n : ℤ)) (-2)).card = n-1 := by
    exact_mod_cast hcard
  simp [faceSeamTopFiber, hnat]

private theorem faceBranchFiber_subset_full (n : ℕ) (hn : 1 ≤ n) :
    faceBranchFiber n ⊆ faceFullCarrier n := by
  intro v hv
  rcases Finset.mem_product.mp hv with ⟨hbase,hk⟩
  have hbase' : v.1 = (0,-1) := by simpa using hbase
  change v ∈ ((faceBaseRange n ×ˢ faceBaseRange n) ×ˢ faceSheetRange n)
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ?_, hk⟩
  have hx : v.1.1 = 0 := by simpa using congrArg Prod.fst hbase'
  have hy : v.1.2 = -1 := by simpa using congrArg Prod.snd hbase'
  constructor <;> simp [faceBaseRange, Finset.mem_Icc] <;> omega

private theorem faceSeamTopFiber_subset_full (n : ℕ) (hn : 1 ≤ n) :
    faceSeamTopFiber n ⊆ faceFullCarrier n := by
  intro v hv
  rcases Finset.mem_product.mp hv with ⟨hbase,hk⟩
  rcases Finset.mem_product.mp hbase with ⟨hx,hy⟩
  have hx' : v.1.1 = 0 := by simpa using hx
  have hk' : v.2 = ((n^5:ℕ):ℤ) := by simpa using hk
  change v ∈ ((faceBaseRange n ×ˢ faceBaseRange n) ×ˢ faceSheetRange n)
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ?_, ?_⟩
  · constructor
    · simp [faceBaseRange, Finset.mem_Icc]
      omega
    · simp [faceBaseRange, Finset.mem_Icc] at hy ⊢
      omega
  · rw [hk']
    simp [faceSheetRange, Finset.mem_Icc]

private theorem faceBranchFiber_disjoint_seamTopFiber (n : ℕ) :
    Disjoint (faceBranchFiber n) (faceSeamTopFiber n) := by
  apply Finset.disjoint_left.mpr
  intro v hv1 hv2
  rcases Finset.mem_product.mp hv1 with ⟨hbase,hk⟩
  rcases Finset.mem_product.mp hv2 with ⟨hbase2,hk2⟩
  rcases Finset.mem_product.mp hbase2 with ⟨hx,hy⟩
  have hbase' : v.1 = (0,-1) := by simpa using hbase
  have hy' : v.1.2 = -1 := by simpa using congrArg Prod.snd hbase'
  have hylt : v.1.2 ≤ -2 := (Finset.mem_Icc.mp hy).2
  omega

private theorem faceFiniteFaces_eq_sdiff (n : ℕ) :
    parafermionicCoverFiniteOrdinaryFaces n =
      faceFullCarrier n \ (faceBranchFiber n ∪ faceSeamTopFiber n) := by
  classical
  apply Finset.ext
  intro v
  rw [Finset.mem_sdiff, Finset.mem_union,
    parafermionicCoverFiniteOrdinaryFaces_mem_iff]
  simp only [faceFullCarrier, faceBaseRange, faceSheetRange,
    faceBranchFiber, faceSeamTopFiber, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_singleton]
  simp only [Nat.cast_pow]
  constructor
  · rintro ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
    refine ⟨⟨⟨⟨hxlo,by omega⟩,⟨hylo,by omega⟩⟩,⟨hklo,hkhi⟩⟩,?_⟩
    intro hbad
    rcases hbad with hbranch | hseambad
    · have hbase' : v.1 = (0,-1) := by simpa using hbranch.1
      exact hnot hbase'
    · have hx := hseambad.1.1
      have hylo' := hseambad.1.2.1
      have hyhi' := hseambad.1.2.2
      have hk := hseambad.2
      have hylt : v.1.2 < -1 := by omega
      have hkEq : v.2 = (n:ℤ)^5 := by omega
      have hstrict := hseam ⟨by simpa using hx,hylt⟩
      omega
  · rintro ⟨⟨⟨⟨hxlo,hxhi⟩,⟨hylo,hyhi⟩⟩,⟨hklo,hkhi⟩⟩,hbad⟩
    have hnot : v.1 ≠ (0,-1) := by
      intro h
      apply hbad
      left
      exact ⟨by simpa using h,⟨by omega,by omega⟩⟩
    have hseam : v.1.1 = 0 ∧ v.1.2 < -1 → v.2 < (n:ℤ)^5 := by
      intro hs
      by_contra hnotlt
      have hkEq : v.2 = (n:ℤ)^5 := by omega
      apply hbad
      right
      exact ⟨⟨by simpa using hs.1, hylo, by omega⟩, hkEq⟩
    exact ⟨hxlo,by omega,hylo,by omega,hklo,hkhi,hnot,by
      intro hs
      have h := hseam hs
      simpa only [Nat.cast_pow] using h⟩

theorem parafermionicCoverFiniteOrdinaryFaces_card (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverFiniteOrdinaryFaces n).card + (2*n^5+1) + (n-1) =
      (2*n)^2 * (2*n^5+1) := by
  classical
  have hsub : faceBranchFiber n ∪ faceSeamTopFiber n ⊆ faceFullCarrier n :=
    Finset.union_subset (faceBranchFiber_subset_full n hn)
      (faceSeamTopFiber_subset_full n hn)
  rw [faceFiniteFaces_eq_sdiff n,
    Finset.card_sdiff_of_subset hsub,
    Finset.card_union_of_disjoint (faceBranchFiber_disjoint_seamTopFiber n),
    faceFullCarrier_card, faceBranchFiber_card, faceSeamTopFiber_card n hn]
  have hn5 : n ≤ n^5 := by nlinarith [Nat.one_le_pow 4 n hn]
  have hbad : (2*n^5+1) + (n-1) ≤ 2*(2*n^5+1) := by omega
  have htotal : 2*(2*n^5+1) ≤ (2*n)^2*(2*n^5+1) := by
    have hn2 : 4 ≤ (2*n)^2 := by nlinarith
    nlinarith
  have hle : (2*n^5+1)+(n-1) ≤ (2*n)^2*(2*n^5+1) := le_trans hbad htotal
  omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
