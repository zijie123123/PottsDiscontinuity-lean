/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleLabelCutIncidence
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial
open scoped BigOperators

noncomputable section

local instance rectangleCutDegreeDualFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) := Fintype.ofFinite _

 theorem mem_rectangleDualExpanded_iff (a : LatticeVertex) (w h : ℕ)
    (z : LatticeVertex) :
    z ∈ rectangleDualExpanded a w h ↔
      a.1 - 1 ≤ z.1 ∧ z.1 ≤ a.1 + (w : ℤ) ∧
      a.2 - 1 ≤ z.2 ∧ z.2 ≤ a.2 + (h : ℤ) := by
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor <;> intro hz <;> omega

def rectangleCutFaceVertex (a : LatticeVertex) (w h : ℕ)
    (x y : ℤ) (hm : (x,y) ∈ rectangleDualExpanded a w h) :
    RectangleDualVertex a w h := ⟨(x,y), hm⟩

def rectangleCutFaceWest (a : LatticeVertex) (w h : ℕ)
    (x y : ℤ) (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) : RectangleDualVertex a w h :=
  rectangleCutFaceVertex a w h (x-1) y
    ((mem_rectangleDualExpanded_iff a w h (x-1,y)).2 ⟨by omega, by omega, by omega, by omega⟩)

def rectangleCutFaceEast (a : LatticeVertex) (w h : ℕ)
    (x y : ℤ) (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) : RectangleDualVertex a w h :=
  rectangleCutFaceVertex a w h (x+1) y
    ((mem_rectangleDualExpanded_iff a w h (x+1,y)).2 ⟨by omega, by omega, by omega, by omega⟩)

def rectangleCutFaceSouth (a : LatticeVertex) (w h : ℕ)
    (x y : ℤ) (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) : RectangleDualVertex a w h :=
  rectangleCutFaceVertex a w h x (y-1)
    ((mem_rectangleDualExpanded_iff a w h (x,y-1)).2 ⟨by omega, by omega, by omega, by omega⟩)

def rectangleCutFaceNorth (a : LatticeVertex) (w h : ℕ)
    (x y : ℤ) (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) : RectangleDualVertex a w h :=
  rectangleCutFaceVertex a w h x (y+1)
    ((mem_rectangleDualExpanded_iff a w h (x,y+1)).2 ⟨by omega, by omega, by omega, by omega⟩)

private theorem rectangleCutDualAdj_iff_of_faceBase (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (b : LatticeBond)
    (hs : b.source ∈ latticeRectangle a w h) (ht : b.target ∈ latticeRectangle a w h)
    (u v : RectangleDualVertex a w h)
    (hfaces : (u.val = b.faceBase false ∧ v.val = b.faceBase true) ∨
      (u.val = b.faceBase true ∧ v.val = b.faceBase false)) :
    (rectangleLabelCutDualGraph a w h σ).Adj u v ↔
      σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
  let d := rectangleCutDualEdgeOfBond a w h b hs ht
  have hg := rectangleCutDualEdgeOfBond_adj_iff a w h σ b hs ht
  rcases hfaces with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · have hu' : u = rectangleDualEdgeSource a w h d := by
      apply Subtype.ext
      exact hu.trans (rectangleCutDualEdgeOfBond_source_val a w h b hs ht).symm
    have hv' : v = rectangleDualEdgeTarget a w h d := by
      apply Subtype.ext
      exact hv.trans (rectangleCutDualEdgeOfBond_target_val a w h b hs ht).symm
    rw [hu', hv']
    exact hg
  · have hu' : u = rectangleDualEdgeTarget a w h d := by
      apply Subtype.ext
      exact hu.trans (rectangleCutDualEdgeOfBond_target_val a w h b hs ht).symm
    have hv' : v = rectangleDualEdgeSource a w h d := by
      apply Subtype.ext
      exact hv.trans (rectangleCutDualEdgeOfBond_source_val a w h b hs ht).symm
    rw [hu', hv']
    have hcomm : (rectangleLabelCutDualGraph a w h σ).Adj
        (rectangleDualEdgeTarget a w h d) (rectangleDualEdgeSource a w h d) ↔
        (rectangleLabelCutDualGraph a w h σ).Adj
          (rectangleDualEdgeSource a w h d) (rectangleDualEdgeTarget a w h d) :=
      ⟨fun h => h.symm, fun h => h.symm⟩
    exact hcomm.trans hg

private theorem rectangleCutFace_east_adj_iff (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (x y : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩))
      (rectangleCutFaceEast a w h x y hx hxw hy hyh) ↔
        σ ⟨(x+1,y), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ !=
          σ ⟨(x+1,y+1), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ := by
  let b : LatticeBond := ⟨(x+1,y), .vertical⟩
  have hs : b.source ∈ latticeRectangle a w h := by
    rw [mem_latticeRectangle]
    simp [b, LatticeBond.source]
    omega
  have ht : b.target ∈ latticeRectangle a w h := by
    rw [mem_latticeRectangle]
    simp [b, LatticeBond.target]
    omega
  have hroute :
      ((rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)).val =
          b.faceBase false ∧
        (rectangleCutFaceEast a w h x y hx hxw hy hyh).val = b.faceBase true) := by
    simp [b, rectangleCutFaceEast, rectangleCutFaceVertex, LatticeBond.faceBase]
  have hgen := rectangleCutDualAdj_iff_of_faceBase a w h σ b hs ht _ _ (Or.inl hroute)
  simpa [b, LatticeBond.source, LatticeBond.target] using hgen

private theorem rectangleCutFace_north_adj_iff (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (x y : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩))
      (rectangleCutFaceNorth a w h x y hx hxw hy hyh) ↔
        σ ⟨(x,y+1), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ !=
          σ ⟨(x+1,y+1), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ := by
  let b : LatticeBond := ⟨(x,y+1), .horizontal⟩
  have hs : b.source ∈ latticeRectangle a w h := by
    rw [mem_latticeRectangle]
    simp [b, LatticeBond.source]
    omega
  have ht : b.target ∈ latticeRectangle a w h := by
    rw [mem_latticeRectangle]
    simp [b, LatticeBond.target]
    omega
  have hroute :
      ((rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)).val =
          b.faceBase false ∧
        (rectangleCutFaceNorth a w h x y hx hxw hy hyh).val = b.faceBase true) := by
    simp [b, rectangleCutFaceNorth, rectangleCutFaceVertex, LatticeBond.faceBase]
  have hgen := rectangleCutDualAdj_iff_of_faceBase a w h σ b hs ht _ _ (Or.inl hroute)
  simpa [b, LatticeBond.source, LatticeBond.target] using hgen

private theorem rectangleCutFace_west_adj_iff (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (x y : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩))
      (rectangleCutFaceWest a w h x y hx hxw hy hyh) ↔
        σ ⟨(x,y), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ !=
          σ ⟨(x,y+1), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ := by
  let b : LatticeBond := ⟨(x,y), .vertical⟩
  have hs : b.source ∈ latticeRectangle a w h := by
    rw [mem_latticeRectangle]
    simp [b, LatticeBond.source]
    omega
  have ht : b.target ∈ latticeRectangle a w h := by
    rw [mem_latticeRectangle]
    simp [b, LatticeBond.target]
    omega
  have hroute :
      ((rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)).val =
          b.faceBase true ∧
        (rectangleCutFaceWest a w h x y hx hxw hy hyh).val = b.faceBase false) := by
    simp [b, rectangleCutFaceWest, rectangleCutFaceVertex, LatticeBond.faceBase]
  have hgen := rectangleCutDualAdj_iff_of_faceBase a w h σ b hs ht _ _ (Or.inr hroute)
  simpa [b, LatticeBond.source, LatticeBond.target] using hgen

private theorem rectangleCutFace_south_adj_iff (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (x y : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩))
      (rectangleCutFaceSouth a w h x y hx hxw hy hyh) ↔
        σ ⟨(x,y), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ !=
          σ ⟨(x+1,y), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ := by
  let b : LatticeBond := ⟨(x,y), .horizontal⟩
  have hs : b.source ∈ latticeRectangle a w h := by
    rw [mem_latticeRectangle]
    simp [b, LatticeBond.source]
    omega
  have ht : b.target ∈ latticeRectangle a w h := by
    rw [mem_latticeRectangle]
    simp [b, LatticeBond.target]
    omega
  have hgeneric := rectangleCutDualEdgeOfBond_adj_iff a w h σ b hs ht
  have hsrc : (rectangleDualEdgeSource a w h
      (rectangleCutDualEdgeOfBond a w h b hs ht)) =
        rectangleCutFaceSouth a w h x y hx hxw hy hyh := by
    apply Subtype.ext
    simpa [b, rectangleCutFaceSouth, rectangleCutFaceVertex, LatticeBond.faceBase]
      using rectangleCutDualEdgeOfBond_source_val a w h b hs ht
  have htgt : (rectangleDualEdgeTarget a w h
      (rectangleCutDualEdgeOfBond a w h b hs ht)) =
        rectangleCutFaceVertex a w h x y
          ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩) := by
    apply Subtype.ext
    simpa [b, rectangleCutFaceVertex, LatticeBond.faceBase]
      using rectangleCutDualEdgeOfBond_target_val a w h b hs ht
  have hcomm : (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩))
      (rectangleCutFaceSouth a w h x y hx hxw hy hyh) ↔
      (rectangleLabelCutDualGraph a w h σ).Adj
        (rectangleCutFaceSouth a w h x y hx hxw hy hyh)
        (rectangleCutFaceVertex a w h x y
          ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)) :=
    ⟨fun h => h.symm, fun h => h.symm⟩
  have hgeneric' : (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleCutFaceSouth a w h x y hx hxw hy hyh)
      (rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)) ↔
      σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
    simpa [hsrc, htgt] using hgeneric
  simpa [b, LatticeBond.source, LatticeBond.target] using hcomm.trans hgeneric'

private theorem rectangleCutFace_adj_neighbor_coordinate (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (x y : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ))
    (v : RectangleDualVertex a w h)
    (hadj : (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)) v) :
    v.val = (x-1,y) ∨ v.val = (x+1,y) ∨ v.val = (x,y-1) ∨ v.val = (x,y+1) := by
  rcases v with ⟨⟨vx,vy⟩, hv_mem⟩
  change (vx,vy) = (x-1,y) ∨ (vx,vy) = (x+1,y) ∨
    (vx,vy) = (x,y-1) ∨ (vx,vy) = (x,y+1)
  obtain ⟨b, hs, ht, hdiff, hroute⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ _ ⟨(vx,vy),hv_mem⟩).mp hadj
  rcases b with ⟨⟨bx,byy⟩, axis⟩
  cases axis
  · simp [LatticeBond.faceBase] at hroute
    simp only [rectangleCutFaceVertex] at hroute
    rcases hroute with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · rcases Prod.mk.inj hu with ⟨hux,huy⟩
      rcases hv with ⟨hvx,hvy⟩
      simp_all
    · rcases Prod.mk.inj hu with ⟨hux,huy⟩
      rcases hv with ⟨hvx,hvy⟩
      simp_all
  · simp [LatticeBond.faceBase] at hroute
    simp only [rectangleCutFaceVertex] at hroute
    rcases hroute with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · rcases Prod.mk.inj hu with ⟨hux,huy⟩
      rcases hv with ⟨hvx,hvy⟩
      simp_all
    · rcases Prod.mk.inj hu with ⟨hux,huy⟩
      rcases hv with ⟨hvx,hvy⟩
      simp_all

def rectangleCutFaceNeighbor (a : LatticeVertex) (w h : ℕ)
    (x y : ℤ) (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) : Fin 4 → RectangleDualVertex a w h :=
  fun i => if i.val = 0 then rectangleCutFaceSouth a w h x y hx hxw hy hyh
    else if i.val = 1 then rectangleCutFaceEast a w h x y hx hxw hy hyh
    else if i.val = 2 then rectangleCutFaceNorth a w h x y hx hxw hy hyh
    else rectangleCutFaceWest a w h x y hx hxw hy hyh

private theorem rectangleCutFaceNeighbor_injective (a : LatticeVertex) (w h : ℕ)
    (x y : ℤ) (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) :
    Function.Injective (rectangleCutFaceNeighbor a w h x y hx hxw hy hyh) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [rectangleCutFaceNeighbor, rectangleCutFaceWest, rectangleCutFaceEast,
      rectangleCutFaceSouth, rectangleCutFaceNorth, rectangleCutFaceVertex] at hij ⊢ <;> omega

local instance rectangleLabelCutDualGraphDecidableAdj (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) :
    DecidableRel (rectangleLabelCutDualGraph a w h σ).Adj := Classical.decRel _

local instance rectangleCutDualNeighborSetFintype (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (v : RectangleDualVertex a w h) :
    Fintype ((rectangleLabelCutDualGraph a w h σ).neighborSet v) := Fintype.ofFinite _

private theorem rectangleCutFace_neighborFinset_eq (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (x y : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).neighborFinset
        (rectangleCutFaceVertex a w h x y
          ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)) =
      (Finset.univ.image (rectangleCutFaceNeighbor a w h x y hx hxw hy hyh)).filter
        ((rectangleLabelCutDualGraph a w h σ).Adj
          (rectangleCutFaceVertex a w h x y
            ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩))) := by
  classical
  let z := rectangleCutFaceVertex a w h x y
    ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)
  let f := rectangleCutFaceNeighbor a w h x y hx hxw hy hyh
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hadj
    refine ⟨?_, hadj⟩
    obtain hcoord := rectangleCutFace_adj_neighbor_coordinate a w h σ x y hx hxw hy hyh v hadj
    rcases hcoord with hw | he | hs | hn
    · exact ⟨(3 : Fin 4), by
        apply Subtype.ext
        simpa [f, rectangleCutFaceNeighbor, rectangleCutFaceWest,
          rectangleCutFaceVertex] using hw.symm⟩
    · exact ⟨(1 : Fin 4), by
        apply Subtype.ext
        simpa [f, rectangleCutFaceNeighbor, rectangleCutFaceEast,
          rectangleCutFaceVertex] using he.symm⟩
    · exact ⟨(0 : Fin 4), by
        apply Subtype.ext
        simpa [f, rectangleCutFaceNeighbor, rectangleCutFaceSouth,
          rectangleCutFaceVertex] using hs.symm⟩
    · exact ⟨(2 : Fin 4), by
        apply Subtype.ext
        simpa [f, rectangleCutFaceNeighbor, rectangleCutFaceNorth,
          rectangleCutFaceVertex] using hn.symm⟩
  · rintro ⟨⟨i, hfi⟩, hadj⟩
    exact hadj

private theorem boolNe_eq_true_symm (b c : Bool) :
    (b != c) = true ↔ (c != b) = true := by
  cases b <;> cases c <;> decide

theorem rectangleLabelCutDual_interior_degree_even (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (x y : ℤ)
    (hx : a.1 ≤ x) (hxw : x < a.1 + (w : ℤ))
    (hy : a.2 ≤ y) (hyh : y < a.2 + (h : ℤ)) :
    Even ((rectangleLabelCutDualGraph a w h σ).degree
      (rectangleCutFaceVertex a w h x y
        ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩))) := by
  classical
  let z := rectangleCutFaceVertex a w h x y
    ((mem_rectangleDualExpanded_iff a w h (x,y)).2 ⟨by omega, by omega, by omega, by omega⟩)
  let f := rectangleCutFaceNeighbor a w h x y hx hxw hy hyh
  let b₀ := σ ⟨(x,y), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  let b₁ := σ ⟨(x+1,y), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  let b₂ := σ ⟨(x+1,y+1), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  let b₃ := σ ⟨(x,y+1), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  have hcard : (rectangleLabelCutDualGraph a w h σ).degree z =
      (Finset.univ.filter (fun i : Fin 4 =>
        (rectangleLabelCutDualGraph a w h σ).Adj z (f i))).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      rectangleCutFace_neighborFinset_eq a w h σ x y hx hxw hy hyh]
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _
      (rectangleCutFaceNeighbor_injective a w h x y hx hxw hy hyh)
  have hsouth : (rectangleLabelCutDualGraph a w h σ).Adj z (f 0) ↔ (b₀ != b₁) = true := by
    simpa [f, rectangleCutFaceNeighbor, z, b₀, b₁] using
      rectangleCutFace_south_adj_iff a w h σ x y hx hxw hy hyh
  have heast : (rectangleLabelCutDualGraph a w h σ).Adj z (f 1) ↔ (b₁ != b₂) = true := by
    simpa [f, rectangleCutFaceNeighbor, z, b₁, b₂] using
      rectangleCutFace_east_adj_iff a w h σ x y hx hxw hy hyh
  have hnorth : (rectangleLabelCutDualGraph a w h σ).Adj z (f 2) ↔ (b₂ != b₃) = true := by
    have hraw : (rectangleLabelCutDualGraph a w h σ).Adj z (f 2) ↔ (b₃ != b₂) = true := by
      simpa [f, rectangleCutFaceNeighbor, z, b₂, b₃] using
        rectangleCutFace_north_adj_iff a w h σ x y hx hxw hy hyh
    exact hraw.trans (boolNe_eq_true_symm b₃ b₂)
  have hwest : (rectangleLabelCutDualGraph a w h σ).Adj z (f 3) ↔ (b₃ != b₀) = true := by
    have hraw : (rectangleLabelCutDualGraph a w h σ).Adj z (f 3) ↔ (b₀ != b₃) = true := by
      simpa [f, rectangleCutFaceNeighbor, z, b₀, b₃] using
        rectangleCutFace_west_adj_iff a w h σ x y hx hxw hy hyh
    exact hraw.trans (boolNe_eq_true_symm b₀ b₃)
  have hsum : (∑ i : Fin 4,
      if (rectangleLabelCutDualGraph a w h σ).Adj z (f i) then 1 else 0) =
      (if b₀ != b₁ then 1 else 0) + (if b₁ != b₂ then 1 else 0) +
        (if b₂ != b₃ then 1 else 0) + (if b₃ != b₀ then 1 else 0) := by
    have hsouth' : (rectangleLabelCutDualGraph a w h σ).Adj z (f (0 : Fin 4)) ↔
        (b₀ != b₁) = true := hsouth
    have heast' : (rectangleLabelCutDualGraph a w h σ).Adj z
        (f (Fin.succ (0 : Fin 3))) ↔ (b₁ != b₂) = true := heast
    have hnorth' : (rectangleLabelCutDualGraph a w h σ).Adj z
        (f (Fin.succ (Fin.succ (0 : Fin 2)))) ↔ (b₂ != b₃) = true := hnorth
    have hwest' : (rectangleLabelCutDualGraph a w h σ).Adj z
        (f (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))) ↔
        (b₃ != b₀) = true := hwest
    simp only [Fin.sum_univ_succ]
    simp only [hsouth', heast', hnorth', hwest']
    ac_rfl
  have hcount : (Finset.univ.filter (fun i : Fin 4 =>
      (rectangleLabelCutDualGraph a w h σ).Adj z (f i))).card =
      ∑ i : Fin 4, if (rectangleLabelCutDualGraph a w h σ).Adj z (f i) then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcard, hcount, hsum]
  exact fourBoolCut_even b₀ b₁ b₃ b₂

end

end PottsDiscontinuity.FK
