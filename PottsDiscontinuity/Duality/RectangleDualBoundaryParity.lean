/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import PottsDiscontinuity.Duality.RectangleLabelCutIncidence

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial
open scoped BigOperators

noncomputable section

/-- The dual port just below the original bottom edge indexed by its horizontal
bond coordinate. `i` is clamped only so the auxiliary vertex is total; in the
port finset we use `i < w`. -/
def rectangleDualBottomPortVertex (a : LatticeVertex) (w h : ℕ) (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 - 1), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- The corresponding dual port just above the original top edge. -/
def rectangleDualTopPortVertex (a : LatticeVertex) (w h : ℕ) (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 + (h : ℤ)), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

def rectangleDualBottomPorts (a : LatticeVertex) (w h : ℕ) :
    Finset (RectangleDualVertex a w h) :=
  (Finset.range w).image (rectangleDualBottomPortVertex a w h)

def rectangleDualTopPorts (a : LatticeVertex) (w h : ℕ) :
    Finset (RectangleDualVertex a w h) :=
  (Finset.range w).image (rectangleDualTopPortVertex a w h)

theorem rectangleDualBottomTopPorts_disjoint (a : LatticeVertex) (w h : ℕ) :
    Disjoint (rectangleDualBottomPorts a w h) (rectangleDualTopPorts a w h) := by
  rw [Finset.disjoint_left]
  intro v hb ht
  rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨j, hj, heq⟩
  have hy := congrArg (fun z : RectangleDualVertex a w h => z.1.2) heq
  simp only [rectangleDualBottomPortVertex, rectangleDualTopPortVertex] at hy
  have hiw := Finset.mem_range.mp hi
  have hjw := Finset.mem_range.mp hj
  omega

lemma rectangleDualBottomPort_val_of_lt (a : LatticeVertex) (w h : ℕ)
    (i : ℕ) (hi : i < w) :
    (rectangleDualBottomPortVertex a w h i).1 = (a.1 + (i : ℤ), a.2 - 1) := by
  change (a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 - 1) = _
  simp only [Nat.min_eq_left (Nat.le_of_lt hi)]

lemma rectangleClampedBottomLabel_val (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i ≤ w) :
    rectangleClampedBottomLabel a w h σ i =
      σ ⟨(a.1 + (i : ℤ), a.2), by rw [mem_latticeRectangle]; constructor <;>
        constructor <;> omega⟩ := by
  simp [rectangleClampedBottomLabel, Nat.min_eq_left hi]

def rectangleDualBottomUpVertex (a : LatticeVertex) (w h : ℕ) (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

lemma rectangleDualBottomUpVertex_val_of_lt (a : LatticeVertex) (w h : ℕ)
    (i : ℕ) (hi : i < w) :
    (rectangleDualBottomUpVertex a w h i).1 = (a.1 + (i : ℤ), a.2) := by
  change (a.1 + ((Nat.min i w : ℕ) : ℤ), a.2) = _
  simp only [Nat.min_eq_left (Nat.le_of_lt hi)]

lemma rectangleDualBottomAdj_implies_up (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i < w)
    (z : RectangleDualVertex a w h)
    (hadj : (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualBottomPortVertex a w h i) z) :
    z = rectangleDualBottomUpVertex a w h i := by
  obtain ⟨b, hs, ht, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ
      (rectangleDualBottomPortVertex a w h i) z).mp hadj
  rcases b with ⟨⟨x,y⟩, axis⟩
  rw [mem_latticeRectangle] at hs ht
  have hport := rectangleDualBottomPort_val_of_lt a w h i hi
  cases axis
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
    rcases hs with ⟨_, ⟨hylower, hyupper⟩⟩
    rw [hport] at huv
    simp only [Prod.mk.injEq] at huv
    rcases huv with ⟨⟨hpx,hpy⟩,hz⟩ | ⟨⟨hpx,hpy⟩,hz⟩
    · have hy : y = a.2 := by omega
      have hx : x = a.1 + (i : ℤ) := by omega
      apply Subtype.ext
      calc
        (z : LatticeVertex) = (x,y) := hz
        _ = (a.1 + (i : ℤ), a.2) := Prod.ext hx hy
        _ = (rectangleDualBottomUpVertex a w h i : LatticeVertex) :=
          (rectangleDualBottomUpVertex_val_of_lt a w h i hi).symm
    · exfalso
      omega
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
    rcases hs with ⟨_, ⟨hylower, hyupper⟩⟩
    rw [hport] at huv
    simp only [Prod.mk.injEq] at huv
    rcases huv with ⟨⟨hpx,hpy⟩,hz⟩ | ⟨⟨hpx,hpy⟩,hz⟩ <;> omega

lemma rectangleDualBottomAdj_iff_up_and_flip (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i < w)
    (z : RectangleDualVertex a w h) :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualBottomPortVertex a w h i) z ↔
      z = rectangleDualBottomUpVertex a w h i ∧
        rectangleClampedBottomLabel a w h σ i !=
          rectangleClampedBottomLabel a w h σ (i + 1) := by
  constructor
  · intro hadj
    have hz := rectangleDualBottomAdj_implies_up a w h σ i hi z hadj
    subst z
    refine ⟨rfl, ?_⟩
    obtain ⟨b, hs, ht, hdiff, huv⟩ :=
      (rectangleLabelCutDual_adj_iff_bond a w h σ
        (rectangleDualBottomPortVertex a w h i)
        (rectangleDualBottomUpVertex a w h i)).mp hadj
    rcases b with ⟨⟨x,y⟩, axis⟩
    have hs0 := hs
    have ht0 := ht
    rw [mem_latticeRectangle] at hs ht
    have hport := rectangleDualBottomPort_val_of_lt a w h i hi
    cases axis
    · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
      rcases hs with ⟨_, ⟨hylower, hyupper⟩⟩
      rcases huv with hcase | hcase
      · have hpx := congrArg Prod.fst hcase.1
        have hpy := congrArg Prod.snd hcase.1
        rw [hport] at hpx hpy
        have hy : y = a.2 := by omega
        have hx : x = a.1 + (i : ℤ) := by omega
        have hi1 : i + 1 ≤ w := Nat.succ_le_of_lt hi
        have hfirst := rectangleClampedBottomLabel_val a w h σ i (Nat.le_of_lt hi)
        have hsecond := rectangleClampedBottomLabel_val a w h σ (i + 1) hi1
        have hsourcePoint : (⟨(a.1 + (i : ℤ), a.2), by
            rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ : RectangleVertex a w h) =
            ⟨(x,y), hs0⟩ := by
          apply Subtype.ext
          exact Prod.ext hx.symm hy.symm
        have htargetPoint : (⟨(a.1 + ((i + 1 : ℕ) : ℤ), a.2), by
            rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ : RectangleVertex a w h) =
            ⟨(x + 1,y), ht0⟩ := by
          apply Subtype.ext
          apply Prod.ext
          · push_cast
            omega
          · exact hy.symm
        have hsecond' : rectangleClampedBottomLabel a w h σ (i + 1) =
            σ ⟨(x + 1,y), ht0⟩ := by
          rw [hsecond]
          exact congrArg σ htargetPoint
        have hfirst' : rectangleClampedBottomLabel a w h σ i = σ ⟨(x,y), hs0⟩ :=
          hfirst.trans (congrArg σ hsourcePoint)
        have hdiff' : σ ⟨(x,y), hs0⟩ != σ ⟨(x + 1,y), ht0⟩ := by
          simpa [LatticeBond.source, LatticeBond.target] using hdiff
        simpa only [hfirst', hsecond'] using hdiff' 
      · exfalso
        have hpx := congrArg Prod.fst hcase.1
        have hpy := congrArg Prod.snd hcase.1
        rw [hport] at hpx hpy
        omega
    · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
      rcases hs with ⟨_, ⟨hylower, hyupper⟩⟩
      have hporty := congrArg Prod.snd hport
      rcases huv with hcase | hcase
      · have hbase := congrArg Prod.snd hcase.1
        omega
      · have hbase := congrArg Prod.snd hcase.1
        omega
  · rintro ⟨rfl, hflip⟩
    let b : LatticeBond := ⟨(a.1 + (i : ℤ), a.2), .horizontal⟩
    have hs : b.source ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]
      simp only [b, LatticeBond.source]
      constructor <;> constructor <;> omega
    have ht : b.target ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]
      simp only [b, LatticeBond.target]
      constructor <;> constructor <;> omega
    have hdiff : σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
      have hi1 : i + 1 ≤ w := Nat.succ_le_of_lt hi
      have hfirst := rectangleClampedBottomLabel_val a w h σ i (Nat.le_of_lt hi)
      have hsecond := rectangleClampedBottomLabel_val a w h σ (i + 1) hi1
      have htargetcoord : (a.1 + ((i + 1 : ℕ) : ℤ), a.2) =
          (a.1 + (i : ℤ) + 1, a.2) := by
        congr 1
        push_cast
        omega
      have hsecond' : rectangleClampedBottomLabel a w h σ (i + 1) =
          σ ⟨(a.1 + (i : ℤ) + 1, a.2), ht⟩ := by
        rw [hsecond]
        apply congrArg σ
        apply Subtype.ext
        exact htargetcoord
      have hfirst' : rectangleClampedBottomLabel a w h σ i = σ ⟨b.source, hs⟩ := by
        rw [hfirst]
        apply congrArg σ
        apply Subtype.ext
        simp [b, LatticeBond.source]
      have htargetPoint : (⟨(a.1 + (i : ℤ) + 1, a.2), ht⟩ : RectangleVertex a w h) =
          ⟨b.target, ht⟩ := by
        apply Subtype.ext
        change (a.1 + (i : ℤ) + 1, a.2) = (a.1 + (i : ℤ) + 1, a.2)
        rfl
      have hsecond'' : rectangleClampedBottomLabel a w h σ (i + 1) =
          σ ⟨b.target, ht⟩ := hsecond'.trans (congrArg σ htargetPoint)
      have hflip' := hflip
      rw [hfirst'] at hflip'
      rw [hsecond''] at hflip'
      exact hflip' 
    have hadj := (rectangleLabelCutDual_adj_iff_bond a w h σ
      (rectangleDualBottomPortVertex a w h i) (rectangleDualBottomUpVertex a w h i)).2
      ⟨b, hs, ht, hdiff, ?_⟩
    · exact hadj
    · apply Or.inl
      constructor
      · rw [rectangleDualBottomPort_val_of_lt a w h i hi]
        simp [b, LatticeBond.faceBase]
      · rw [rectangleDualBottomUpVertex_val_of_lt a w h i hi]
        simp [b, LatticeBond.faceBase]

end

local instance rectangleDualVertexFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) :=
  Fintype.ofFinset (rectangleDualExpanded a w h) (fun _ => Iff.rfl)

noncomputable local instance rectangleLabelCutNeighborFintype (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (v : RectangleDualVertex a w h) :
    Fintype ((rectangleLabelCutDualGraph a w h σ).neighborSet v) := by
  classical
  exact Fintype.ofFinset
    ((Finset.univ : Finset (RectangleDualVertex a w h)).filter
      fun z => (rectangleLabelCutDualGraph a w h σ).Adj v z)
    (by intro z; simp [SimpleGraph.neighborSet])

theorem rectangleDualBottomPort_degree (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i < w) :
    (rectangleLabelCutDualGraph a w h σ).degree (rectangleDualBottomPortVertex a w h i) =
      if rectangleClampedBottomLabel a w h σ i !=
          rectangleClampedBottomLabel a w h σ (i + 1) then 1 else 0 := by
  classical
  let G := rectangleLabelCutDualGraph a w h σ
  let u := rectangleDualBottomPortVertex a w h i
  let v := rectangleDualBottomUpVertex a w h i
  let L := rectangleClampedBottomLabel a w h σ i
  let R := rectangleClampedBottomLabel a w h σ (i + 1)
  have huv : ∀ z, G.Adj u z ↔
      z = v ∧ (L != R) = true := by
    intro z
    exact rectangleDualBottomAdj_iff_up_and_flip a w h σ i hi z
  have hne : v ≠ u := by
    intro he
    have hy := congrArg (fun z : RectangleDualVertex a w h => z.1.2) he
    simp [u, v, rectangleDualBottomPortVertex, rectangleDualBottomUpVertex] at hy
    omega
  rw [← G.card_neighborFinset_eq_degree]
  have hset : G.neighborFinset u = if h : L = R then ∅ else {v} := by
    ext z
    rw [G.mem_neighborFinset]
    rw [huv z]
    by_cases h : L = R <;> simp [h]
  rw [hset]
  by_cases h : L = R <;> simp [L, R, h]

theorem rectangleDualLeftColumn_isolated (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 → σ v = true)
    (z : RectangleDualVertex a w h) (hz : z.1.1 = a.1 - 1) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨b, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  rcases b with ⟨⟨x,y0⟩,axis⟩
  have hsMem := hs0
  have htMem := ht0
  have hportX : z.1.1 = a.1 - 1 := hz
  rw [mem_latticeRectangle] at hs0 ht0
  cases axis
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    rcases huv with hcase | hcase
    · have hfx := congrArg Prod.fst hcase.1
      omega
    · have hfx := congrArg Prod.fst hcase.1
      omega
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    rcases huv with hcase | hcase
    · have hfx := congrArg Prod.fst hcase.1
      have hx : x = a.1 := by omega
      have hsx : (LatticeBond.source ⟨(x,y0), .vertical⟩).1 = a.1 := by simp [LatticeBond.source, hx]
      have htx : (LatticeBond.target ⟨(x,y0), .vertical⟩).1 = a.1 := by simp [LatticeBond.target, hx]
      have hσs := hleft ⟨(x,y0), hsMem⟩ hsx
      have hσt := hleft ⟨(x,y0+1), htMem⟩ htx
      change σ ⟨(x,y0), hsMem⟩ != σ ⟨(x,y0+1), htMem⟩ at hdiff
      simp [hσs, hσt] at hdiff
    · have hfx := congrArg Prod.fst hcase.1
      have hx : x = a.1 - 1 := by omega
      omega

theorem rectangleDualRightColumn_isolated (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hright : ∀ v : RectangleVertex a w h,
      v.1.1 = a.1 + (w : ℤ) → σ v = false)
    (z : RectangleDualVertex a w h) (hz : z.1.1 = a.1 + (w : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨b, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  rcases b with ⟨⟨x,y0⟩,axis⟩
  have hsMem := hs0
  have htMem := ht0
  have hportX : z.1.1 = a.1 + (w : ℤ) := hz
  rw [mem_latticeRectangle] at hs0 ht0
  cases axis
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    rcases huv with hcase | hcase
    · have hfx := congrArg Prod.fst hcase.1
      omega
    · have hfx := congrArg Prod.fst hcase.1
      omega
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    rcases huv with hcase | hcase
    · have hfx := congrArg Prod.fst hcase.1
      have hx : x = a.1 + (w : ℤ) + 1 := by omega
      omega
    · have hfx := congrArg Prod.fst hcase.1
      have hx : x = a.1 + (w : ℤ) := by omega
      have hsx : (LatticeBond.source ⟨(x,y0), .vertical⟩).1 = a.1 + (w : ℤ) := by simp [LatticeBond.source, hx]
      have htx : (LatticeBond.target ⟨(x,y0), .vertical⟩).1 = a.1 + (w : ℤ) := by simp [LatticeBond.target, hx]
      have hσs := hright ⟨(x,y0), hsMem⟩ hsx
      have hσt := hright ⟨(x,y0+1), htMem⟩ htx
      change σ ⟨(x,y0), hsMem⟩ != σ ⟨(x,y0+1), htMem⟩ at hdiff
      simp [hσs, hσt] at hdiff

theorem rectangleDualBottomPortDegreeSum_odd (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩) :
    Odd (∑ i ∈ Finset.range w,
      (rectangleLabelCutDualGraph a w h σ).degree
        (rectangleDualBottomPortVertex a w h i)) := by
  have hsum : (∑ i ∈ Finset.range w,
      (rectangleLabelCutDualGraph a w h σ).degree
        (rectangleDualBottomPortVertex a w h i)) =
      ∑ i ∈ Finset.range w,
        if rectangleClampedBottomLabel a w h σ i !=
            rectangleClampedBottomLabel a w h σ (i + 1) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact rectangleDualBottomPort_degree a w h σ i (Finset.mem_range.mp hi)
  rw [hsum]
  exact rectangleBottomRow_flipCount_odd a w h σ hends

lemma rectangleDualBottomPortVertex_injOn_range (a : LatticeVertex) (w h : ℕ) :
    Set.InjOn (rectangleDualBottomPortVertex a w h) (Finset.range w : Set ℕ) := by
  intro i hi j hj heq
  have hix := congrArg (fun z : RectangleDualVertex a w h => z.1.1) heq
  rw [rectangleDualBottomPort_val_of_lt a w h i (Finset.mem_range.mp hi),
    rectangleDualBottomPort_val_of_lt a w h j (Finset.mem_range.mp hj)] at hix
  exact_mod_cast (add_left_cancel hix)

theorem rectangleDualBottomPortsDegreeSum_odd (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩) :
    Odd (∑ v ∈ rectangleDualBottomPorts a w h,
      (rectangleLabelCutDualGraph a w h σ).degree v) := by
  have himage : (∑ v ∈ rectangleDualBottomPorts a w h,
      (rectangleLabelCutDualGraph a w h σ).degree v) =
      ∑ i ∈ Finset.range w,
        (rectangleLabelCutDualGraph a w h σ).degree
          (rectangleDualBottomPortVertex a w h i) := by
    simpa only [rectangleDualBottomPorts] using
      (Finset.sum_image
        (f := fun v : RectangleDualVertex a w h =>
          (rectangleLabelCutDualGraph a w h σ).degree v)
        (s := Finset.range w)
        (g := rectangleDualBottomPortVertex a w h)
        (rectangleDualBottomPortVertex_injOn_range a w h))
  rw [himage]
  exact rectangleDualBottomPortDegreeSum_odd a w h σ hends

end PottsDiscontinuity.FK
