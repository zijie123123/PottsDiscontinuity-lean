/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.PrimalDualSegments
public import PottsDiscontinuity.Duality.RectangleDualAmbient
public import PottsDiscontinuity.Duality.RectangleDualPotential
public import PottsDiscontinuity.Duality.RectangleEvents
public import PottsDiscontinuity.Duality.RectanglePathIntersection
public import PottsDiscontinuity.Duality.RectangleWalks

@[expose] public section

namespace PottsDiscontinuity.FK
open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial PottsDiscontinuity.FK.Curves unitInterval
noncomputable section

/-- Actual bottom-to-top crossing by complementary dual edges, with endpoints
on the genuine lower and upper face-base rows of the expanded rectangle. -/
def rectangleComplementDualVerticalCrossingEvent (a : LatticeVertex) (w h : ℕ) :
    Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ u v : RectangleDualVertex a w h,
    u.1.2 = a.2 - 1 ∧ v.1.2 = a.2 + (h : ℤ) ∧
    ActualConnected (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A) u v}

def exclusionMesh : PositiveMesh := ⟨1, by norm_num⟩
def exclusionOffset : ℂ := ((1 : ℂ) + Complex.I) / (2 : ℂ)

def rectangleDualOpenGraphToSquare (a : LatticeVertex) (w h : ℕ)
    (D : Configuration (rectangleDualGraph a w h)) :
    openGraph (rectangleDualGraph a w h) D →g squareLattice where
  toFun := fun v => v.1
  map_rel' := by
    intro u v huv
    exact (rectangleDualAmbientGraph_adj_iff a w h _ _).mp
      (rectangleDualGraph_le_ambient a w h (openGraph_le _ _ huv))

private theorem walk_edge_mem_step {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ x y : V, G.Adj x y ∧ e = s(x,y) := by
  induction p with
  | @nil u => simp at he
  | @cons u v w hadj p ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · exact ⟨u,v,hadj,he⟩
      · obtain ⟨x,y,hxy,heq⟩ := ih he
        exact ⟨x,y,hxy,heq⟩

private theorem mapped_walk_edge_mem_step {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G →g H) {u v : V} (p : G.Walk u v)
    {x y : W} (he : s(x,y) ∈ (p.map f).edges) :
    ∃ x' y' : V, G.Adj x' y' ∧ s(x',y') ∈ p.edges ∧
      (f x' = x ∧ f y' = y ∨ f x' = y ∧ f y' = x) := by
  rw [SimpleGraph.Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨e, he, hemap⟩
  obtain ⟨x',y',hadj,heq⟩ := walk_edge_mem_step p he
  rw [heq] at he
  have hpair : s(f x', f y') = s(x,y) := by
    simpa [heq] using hemap
  rcases Sym2.eq_iff.mp hpair with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨x',y',hadj,he,Or.inl ⟨h₁,h₂⟩⟩
  · exact ⟨x',y',hadj,he,Or.inr ⟨h₁,h₂⟩⟩

private theorem latticeWalkPath_range_actual_segment
    {u v : LatticeVertex} (p : squareLattice.Walk u v) (hne : 0 < p.length)
    {z : ℂ} (hz : z ∈ Set.range (latticeWalkPath exclusionMesh p)) :
    ∃ x y : LatticeVertex, x ∈ p.support ∧ y ∈ p.support ∧
      s(x,y) ∈ p.edges ∧ squareLattice.Adj x y ∧
      z ∈ Set.range (Path.segment (latticeEmbed exclusionMesh x)
        (latticeEmbed exclusionMesh y)) := by
  induction p with
  | @nil u => simp at hne
  | @cons u v w hadj p ih =>
      change z ∈ Set.range
        ((Path.segment (latticeEmbed exclusionMesh u) (latticeEmbed exclusionMesh v)).trans
          (latticeWalkPath exclusionMesh p)) at hz
      rw [Path.trans_range] at hz
      rcases hz with hfirst | htail
      · refine ⟨u,v,by simp, ?_⟩
        refine ⟨List.mem_cons.mpr (Or.inr (SimpleGraph.Walk.start_mem_support p)), ?_⟩
        exact ⟨by simp, hadj, hfirst⟩
      · by_cases hlen : p.length = 0
        · have hvw : v = w := SimpleGraph.Walk.eq_of_length_eq_zero hlen
          subst w
          have hpNil : p = SimpleGraph.Walk.nil :=
            (SimpleGraph.Walk.eq_nil_iff_nil).2 (SimpleGraph.Walk.length_eq_zero_iff.mp hlen)
          subst p
          have hvz : z = latticeEmbed exclusionMesh v := by
            rcases htail with ⟨t, ht⟩
            simpa [latticeWalkPath] using ht.symm
          subst z
          refine ⟨u,v,by simp, by simp, ?_⟩
          refine ⟨by simp, hadj, ?_⟩
          rw [Path.range_segment]
          exact right_mem_segment ℝ _ _
        · obtain ⟨x,y,hx,hy,he,hxy,hseg⟩ := ih (by omega) htail
          refine ⟨x,y,List.mem_cons.mpr (Or.inr hx), ?_⟩
          refine ⟨List.mem_cons.mpr (Or.inr hy), ?_⟩
          exact ⟨List.mem_cons.mpr (Or.inr he), hxy, hseg⟩

private theorem rectanglePrimalWalk_segment_edge_label
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v)
    {x y : LatticeVertex}
    (he : s(x,y) ∈ (p.map (rectangleOpenGraphToSquare a w h A)).edges) :
    ∃ e : rectanglePrimalEdgeCarrier a w h,
      e ∈ A ∧ (rectanglePrimalEdgeBond a w h e).toSym2 = s(x,y) := by
  obtain ⟨X,Y,hXY,hEdge,hmap⟩ :=
    mapped_walk_edge_mem_step (rectangleOpenGraphToSquare a w h A) p he
  have hOpen : s(X,Y) ∈ openEdges (rectangleGraph a w h) A := by
    rw [← openGraph_edgeSet]
    exact p.edges_subset_edgeSet hEdge
  change ∃ e : (rectangleGraph a w h).edgeSet,
    e ∈ (A : Set (rectangleGraph a w h).edgeSet) ∧ (e : Sym2 _) = s(X,Y) at hOpen
  rcases hOpen with ⟨e, heA, heval⟩
  have hbond : (rectanglePrimalEdgeBond a w h e).toSym2 = s(X.val,Y.val) := by
    have hh := rectanglePrimalEdgeBond_toSym2_public a w h e
    simpa [heval] using hh
  rcases hmap with hmap | hmap
  · rcases hmap with ⟨rfl,rfl⟩
    exact ⟨e,heA,hbond⟩
  · rcases hmap with ⟨hX,hY⟩
    change X.val = y at hX
    change Y.val = x at hY
    have hsymm : s(X.val,Y.val) = s(x,y) := by
      rw [hX, hY]
      exact Sym2.eq_swap
    exact ⟨e,heA,hbond.trans hsymm⟩

private theorem rectangleDualWalk_segment_edge_label
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v)
    {x y : LatticeVertex}
    (he : s(x,y) ∈ (q.map (rectangleDualOpenGraphToSquare a w h
      (rectangleDualConfiguration a w h A))).edges) :
    ∃ e : RectangleDualEdgeCarrier a w h,
      e.primalEdge ∉ A ∧ e.crossingBond.toSym2 = s(x,y) := by
  let D := rectangleDualConfiguration a w h A
  obtain ⟨X,Y,hXY,hEdge,hmap⟩ :=
    mapped_walk_edge_mem_step (rectangleDualOpenGraphToSquare a w h D) q he
  have hOpen : s(X,Y) ∈ openEdges (rectangleDualGraph a w h) D := by
    rw [← openGraph_edgeSet]
    exact q.edges_subset_edgeSet hEdge
  change ∃ g : (rectangleDualGraph a w h).edgeSet,
    g ∈ (D : Set (rectangleDualGraph a w h).edgeSet) ∧ (g : Sym2 _) = s(X,Y) at hOpen
  rcases hOpen with ⟨g,hg,hgval⟩
  let e := (rectangleDualGraphEdgeEquiv a w h).symm g
  have heq : rectangleDualGraphEdgeEquiv a w h e = g := Equiv.apply_symm_apply _ _
  have hmem : rectangleDualGraphEdgeEquiv a w h e ∈ D := by simpa [heq] using hg
  have hclosed : e.primalEdge ∉ A := (mem_rectangleDualConfiguration a w h A e).mp hmem
  have hpair : e.crossingBond.toSym2 = s(X.val,Y.val) := by
    have hpair' := congrArg Subtype.val heq
    change rectangleDualCarrierPair a w h e = (g : Sym2 _) at hpair'
    rw [hgval] at hpair'
    have hm := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) hpair'
    simpa [rectangleDualCarrierPair, LatticeBond.toSym2,
      rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val] using hm
  rcases hmap with hmap | hmap
  · rcases hmap with ⟨hX,hY⟩
    change X.val = x at hX
    change Y.val = y at hY
    exact ⟨e,hclosed,hpair.trans (by rw [hX,hY])⟩
  · rcases hmap with ⟨hX,hY⟩
    change X.val = y at hX
    change Y.val = x at hY
    exact ⟨e,hclosed,hpair.trans (by rw [hX,hY]; exact Sym2.eq_swap)⟩

private theorem dualCenterSegment_subset_label
    (d : LatticeBond) {x y : LatticeVertex}
    (hpair : d.toSym2 = s(x,y)) :
    Set.range (Path.segment (dualFaceCenter exclusionMesh x)
      (dualFaceCenter exclusionMesh y)) ⊆ dualBondSegment exclusionMesh d := by
  have hends : (d.source = x ∧ d.target = y) ∨
      (d.source = y ∧ d.target = x) := by
    simpa [LatticeBond.toSym2] using Sym2.eq_iff.mp hpair
  rw [Path.range_segment]
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · intro z hz
    exact hz
  · intro z hz
    exact (segment_symm ℝ _ _).subset hz

private theorem latticeSegment_subset_primalBond
    (b : LatticeBond) {x y : LatticeVertex}
    (hpair : b.toSym2 = s(x,y)) :
    Set.range (Path.segment (latticeEmbed exclusionMesh x)
      (latticeEmbed exclusionMesh y)) ⊆ primalBondSegment exclusionMesh b := by
  have hends : (b.source = x ∧ b.target = y) ∨
      (b.source = y ∧ b.target = x) := by
    simpa [LatticeBond.toSym2] using Sym2.eq_iff.mp hpair
  rw [Path.range_segment, primalBondSegment]
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · intro z hz
    exact hz
  · intro z hz
    exact (segment_symm ℝ _ _).subset hz

def rectangleExtendedPrimalWalkPath (a : LatticeVertex) (w : ℕ)
    {u v : LatticeVertex} (p : squareLattice.Walk u v) : Path
      (latticeEmbed exclusionMesh (a.1 - 1,u.2))
      (latticeEmbed exclusionMesh (a.1 + (w : ℤ) + 1,v.2)) :=
  (Path.segment (latticeEmbed exclusionMesh (a.1 - 1,u.2))
      (latticeEmbed exclusionMesh u)).trans
    ((latticeWalkPath exclusionMesh p).trans
      (Path.segment (latticeEmbed exclusionMesh v)
        (latticeEmbed exclusionMesh (a.1 + (w : ℤ) + 1,v.2))))

def rectangleDualCenterWalkPath : {u v : LatticeVertex} →
    squareLattice.Walk u v → Path (dualFaceCenter exclusionMesh u)
      (dualFaceCenter exclusionMesh v)
  | _, _, .nil => Path.refl _
  | u, _, .cons (v := v) _ p =>
      (Path.segment (dualFaceCenter exclusionMesh u)
        (dualFaceCenter exclusionMesh v)).trans (rectangleDualCenterWalkPath p)

def exclusionComplexToPair (z : ℂ) : ℝ × ℝ := (z.re,z.im)

private theorem continuous_exclusionComplexToPair : Continuous exclusionComplexToPair := by
  change Continuous (fun z : ℂ => (z.re,z.im))
  fun_prop

private theorem exclusion_segment_coordinate_bounds
    (z₁ z₂ : ℂ) {z : ℂ} {l r d top : ℝ}
    (hz : z ∈ segment ℝ z₁ z₂)
    (hl₁ : l ≤ z₁.re) (hl₂ : l ≤ z₂.re)
    (hr₁ : z₁.re ≤ r) (hr₂ : z₂.re ≤ r)
    (hd₁ : d ≤ z₁.im) (hd₂ : d ≤ z₂.im)
    (ht₁ : z₁.im ≤ top) (ht₂ : z₂.im ≤ top) :
    l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ top := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t,ht,rfl⟩
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  constructor
  · nlinarith [ht.1,ht.2]
  constructor
  · nlinarith [ht.1,ht.2]
  constructor
  · nlinarith [ht.1,ht.2]
  · nlinarith [ht.1,ht.2]

private theorem rectangleDualWalk_support_in_expanded
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v)
    {x : LatticeVertex}
    (hx : x ∈ (q.map (rectangleDualOpenGraphToSquare a w h
      (rectangleDualConfiguration a w h A))).support) :
    a.1 - 1 ≤ x.1 ∧ x.1 ≤ a.1 + (w : ℤ) ∧
      a.2 - 1 ≤ x.2 ∧ x.2 ≤ a.2 + (h : ℤ) := by
  rw [SimpleGraph.Walk.support_map] at hx
  rcases List.mem_map.mp hx with ⟨z,hz,rfl⟩
  have hzbox := z.property
  simp [rectangleDualExpanded, latticeRectangle] at hzbox
  change a.1 - 1 ≤ z.val.1 ∧ z.val.1 ≤ a.1 + (w : ℤ) ∧
    a.2 - 1 ≤ z.val.2 ∧ z.val.2 ≤ a.2 + (h : ℤ)
  omega

private theorem rectangleDualCenterWalkPath_range_actual_segment
    {u v : LatticeVertex} (p : squareLattice.Walk u v) (hne : 0 < p.length)
    {z : ℂ} (hz : z ∈ Set.range (rectangleDualCenterWalkPath p)) :
    ∃ x y : LatticeVertex, x ∈ p.support ∧ y ∈ p.support ∧
      s(x,y) ∈ p.edges ∧ squareLattice.Adj x y ∧
      z ∈ Set.range (Path.segment (dualFaceCenter exclusionMesh x)
        (dualFaceCenter exclusionMesh y)) := by
  induction p with
  | @nil u => simp at hne
  | @cons u v w hadj p ih =>
      change z ∈ Set.range
        ((Path.segment (dualFaceCenter exclusionMesh u)
          (dualFaceCenter exclusionMesh v)).trans (rectangleDualCenterWalkPath p)) at hz
      rw [Path.trans_range] at hz
      rcases hz with hfirst | htail
      · refine ⟨u,v,by simp, ?_⟩
        refine ⟨List.mem_cons.mpr (Or.inr (SimpleGraph.Walk.start_mem_support p)), ?_⟩
        exact ⟨by simp, hadj, hfirst⟩
      · by_cases hlen : p.length = 0
        · have hvw : v = w := SimpleGraph.Walk.eq_of_length_eq_zero hlen
          subst w
          have hpNil : p = SimpleGraph.Walk.nil :=
            (SimpleGraph.Walk.eq_nil_iff_nil).2 (SimpleGraph.Walk.length_eq_zero_iff.mp hlen)
          subst p
          have hvz : z = dualFaceCenter exclusionMesh v := by
            rcases htail with ⟨t, ht⟩
            simpa [rectangleDualCenterWalkPath] using ht.symm
          subst z
          refine ⟨u,v,by simp, by simp, ?_⟩
          refine ⟨by simp, hadj, ?_⟩
          rw [Path.range_segment]
          exact right_mem_segment ℝ _ _
        · obtain ⟨x,y,hx,hy,he,hxy,hseg⟩ := ih (by omega) htail
          refine ⟨x,y,List.mem_cons.mpr (Or.inr hx), ?_⟩
          refine ⟨List.mem_cons.mpr (Or.inr hy), ?_⟩
          exact ⟨List.mem_cons.mpr (Or.inr he), hxy, hseg⟩

private theorem dualFaceCenter_avoids_latticeVertex
    (x u : LatticeVertex) : dualFaceCenter exclusionMesh u ≠ latticeEmbed exclusionMesh x := by
  let b : LatticeBond := ⟨u, .horizontal⟩
  have hc : dualFaceCenter exclusionMesh u ∈ dualBondSegment exclusionMesh b := by
    change dualFaceCenter exclusionMesh u ∈
      segment ℝ (dualFaceCenter exclusionMesh u) (dualFaceCenter exclusionMesh b.target)
    exact left_mem_segment ℝ _ _
  intro heq
  apply latticeVertex_not_mem_dualBondSegment exclusionMesh x b
  simpa [heq] using hc

private theorem rectangleDualCenterWalkPath_avoids_vertex
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v)
    (x : LatticeVertex) (t : I) :
    rectangleDualCenterWalkPath (q.map (rectangleDualOpenGraphToSquare a w h
      (rectangleDualConfiguration a w h A))) t ≠ latticeEmbed exclusionMesh x := by
  let qm := q.map (rectangleDualOpenGraphToSquare a w h
    (rectangleDualConfiguration a w h A))
  by_cases hzero : qm.length = 0
  · have huv : u.1 = v.1 := by
      have hmap := SimpleGraph.Walk.eq_of_length_eq_zero hzero
      change u.1 = v.1 at hmap
      exact hmap
    have huv' : u = v := Subtype.ext huv
    subst v
    have hqnil : qm = SimpleGraph.Walk.nil := by
      apply SimpleGraph.Walk.eq_nil_iff_nil.mpr
      exact SimpleGraph.Walk.length_eq_zero_iff.mp hzero
    intro heq
    have hq : q.map (rectangleDualOpenGraphToSquare a w h
        (rectangleDualConfiguration a w h A)) = SimpleGraph.Walk.nil := by
      simpa [qm] using hqnil
    rw [hq] at heq
    change dualFaceCenter exclusionMesh u.1 = latticeEmbed exclusionMesh x at heq
    exact dualFaceCenter_avoids_latticeVertex x u.1 heq
  · have hpos : 0 < qm.length := Nat.pos_of_ne_zero hzero
    intro heq
    have hbase := rectangleDualCenterWalkPath_range_actual_segment qm hpos
      (show (rectangleDualCenterWalkPath qm t) ∈
        Set.range (rectangleDualCenterWalkPath qm) from ⟨t,rfl⟩)
    obtain ⟨x₁,y₁,hx,hy,hedge,hadj,hseg⟩ := hbase
    obtain ⟨e,hclosed,hpair⟩ := rectangleDualWalk_segment_edge_label a w h A q hedge
    have hsegCenter : rectangleDualCenterWalkPath qm t ∈
        dualBondSegment exclusionMesh e.crossingBond :=
      dualCenterSegment_subset_label e.crossingBond hpair hseg
    have hvertex : latticeEmbed exclusionMesh x ∈
        dualBondSegment exclusionMesh e.crossingBond := by
      rw [← heq]
      exact hsegCenter
    exact latticeVertex_not_mem_dualBondSegment exclusionMesh x e.crossingBond hvertex

private theorem integer_half_lower (a x : ℤ) (h : a - 1 ≤ x) :
    (a : ℝ) - 1 / 2 ≤ (x : ℝ) + 1 / 2 := by
  have h' : (a : ℝ) - 1 ≤ (x : ℝ) := by exact_mod_cast h
  linarith

private theorem integer_half_upper (a x : ℤ) (w : ℕ)
    (h : x ≤ a + (w : ℤ)) :
    (x : ℝ) + 1 / 2 ≤ (a + (w : ℤ) : ℝ) + 1 / 2 := by
  have h' : (x : ℝ) ≤ (a + (w : ℤ) : ℝ) := by exact_mod_cast h
  linarith

private theorem rectangleOpenWalkPath_coordinates
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) (t : I) :
    (a.1 : ℝ) ≤ (latticeWalkPath exclusionMesh
      (p.map (rectangleOpenGraphToSquare a w h A)) t).re ∧
      (latticeWalkPath exclusionMesh (p.map (rectangleOpenGraphToSquare a w h A)) t).re ≤
        ((a.1 + (w : ℤ)) : ℝ) ∧
      (a.2 : ℝ) ≤ (latticeWalkPath exclusionMesh
        (p.map (rectangleOpenGraphToSquare a w h A)) t).im ∧
      (latticeWalkPath exclusionMesh (p.map (rectangleOpenGraphToSquare a w h A)) t).im ≤
        ((a.2 + (h : ℤ)) : ℝ) := by
  apply latticeWalkPath_coordinate_bounds
  intro x hx
  obtain ⟨z,hz,rfl⟩ := rectangleOpenWalk_mapped_support_preimage a w h A p hx
  have hzbox := (mem_latticeRectangle a z w h).mp z.property
  exact ⟨by exact_mod_cast hzbox.1.1, by exact_mod_cast hzbox.1.2,
    by exact_mod_cast hzbox.2.1, by exact_mod_cast hzbox.2.2⟩

private theorem rectangleDualCenterWalkPath_coordinates
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v)
    (hpos : 0 < (q.map (rectangleDualOpenGraphToSquare a w h
      (rectangleDualConfiguration a w h A))).length) (t : I) :
    ((a.1 : ℝ) - 1 / 2) ≤
        (rectangleDualCenterWalkPath (q.map (rectangleDualOpenGraphToSquare a w h
          (rectangleDualConfiguration a w h A))) t).re ∧
      (rectangleDualCenterWalkPath (q.map (rectangleDualOpenGraphToSquare a w h
        (rectangleDualConfiguration a w h A))) t).re ≤
          ((a.1 + (w : ℤ) : ℝ) + 1 / 2) ∧
      ((a.2 : ℝ) - 1 / 2) ≤
        (rectangleDualCenterWalkPath (q.map (rectangleDualOpenGraphToSquare a w h
          (rectangleDualConfiguration a w h A))) t).im ∧
      (rectangleDualCenterWalkPath (q.map (rectangleDualOpenGraphToSquare a w h
        (rectangleDualConfiguration a w h A))) t).im ≤
          ((a.2 + (h : ℤ) : ℝ) + 1 / 2) := by
  let qm := q.map (rectangleDualOpenGraphToSquare a w h
    (rectangleDualConfiguration a w h A))
  obtain ⟨x,y,hx,hy,hedge,hadj,hseg⟩ :=
    rectangleDualCenterWalkPath_range_actual_segment qm hpos ⟨t,rfl⟩
  have hxbox := rectangleDualWalk_support_in_expanded a w h A q hx
  have hybox := rectangleDualWalk_support_in_expanded a w h A q hy
  rw [Path.range_segment] at hseg
  have hcoord := exclusion_segment_coordinate_bounds
    (l := (a.1 : ℝ) - 1 / 2)
    (r := ((a.1 + (w : ℤ) : ℤ) : ℝ) + 1 / 2)
    (d := (a.2 : ℝ) - 1 / 2)
    (top := ((a.2 + (h : ℤ) : ℤ) : ℝ) + 1 / 2)
    (dualFaceCenter exclusionMesh x) (dualFaceCenter exclusionMesh y) hseg
    (by simp [dualFaceCenter, latticeEmbed, exclusionMesh]; have hh := integer_half_lower a.1 x.1 hxbox.1; linarith)
    (by simp [dualFaceCenter, latticeEmbed, exclusionMesh]; have hh := integer_half_lower a.1 y.1 hybox.1; linarith)
    (by simp [dualFaceCenter, latticeEmbed, exclusionMesh]; have hh := integer_half_upper a.1 x.1 w hxbox.2.1; norm_num at hh ⊢; linarith)
    (by simp [dualFaceCenter, latticeEmbed, exclusionMesh]; have hh := integer_half_upper a.1 y.1 w hybox.2.1; norm_num at hh ⊢; linarith)
    (by simp [dualFaceCenter, latticeEmbed, exclusionMesh]; have hh := integer_half_lower a.2 x.2 hxbox.2.2.1; linarith)
    (by simp [dualFaceCenter, latticeEmbed, exclusionMesh]; have hh := integer_half_lower a.2 y.2 hybox.2.2.1; linarith)
    (by simp [dualFaceCenter, latticeEmbed, exclusionMesh]; have hh := integer_half_upper a.2 x.2 h hxbox.2.2.2; norm_num at hh ⊢; linarith)
    (by simp [dualFaceCenter, latticeEmbed, exclusionMesh]; have hh := integer_half_upper a.2 y.2 h hybox.2.2.2; norm_num at hh ⊢; linarith)
  simpa [qm] using hcoord

private theorem rectangleExtendedPrimalWalkPath_coordinates
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v)
    (hu : u.1.1 = a.1) (hv : v.1.1 = a.1 + (w : ℤ)) (t : I) :
    ((a.1 : ℝ) - 1) ≤ (rectangleExtendedPrimalWalkPath a w
      (p.map (rectangleOpenGraphToSquare a w h A)) t).re ∧
      (rectangleExtendedPrimalWalkPath a w
        (p.map (rectangleOpenGraphToSquare a w h A)) t).re ≤
          ((a.1 + (w : ℤ) : ℝ) + 1) ∧
      ((a.2 : ℝ) - 1 / 2) ≤ (rectangleExtendedPrimalWalkPath a w
        (p.map (rectangleOpenGraphToSquare a w h A)) t).im ∧
      (rectangleExtendedPrimalWalkPath a w
        (p.map (rectangleOpenGraphToSquare a w h A)) t).im ≤
          ((a.2 + (h : ℤ) : ℝ) + 1 / 2) := by
  let ps := p.map (rectangleOpenGraphToSquare a w h A)
  let left : LatticeVertex := (a.1 - 1,u.1.2)
  let right : LatticeVertex := (a.1 + (w : ℤ) + 1,v.1.2)
  have huBox := (mem_latticeRectangle a u.1 w h).mp u.2
  have hvBox := (mem_latticeRectangle a v.1 w h).mp v.2
  have hmid := rectangleOpenWalkPath_coordinates a w h A p t
  have huX : (u.1.1 : ℝ) = (a.1 : ℝ) := by exact_mod_cast hu
  have hvX : (v.1.1 : ℝ) = (a.1 + (w : ℤ) : ℝ) := by exact_mod_cast hv
  have huYlo : (a.2 : ℝ) ≤ (u.1.2 : ℝ) := by exact_mod_cast huBox.2.1
  have huYhi : (u.1.2 : ℝ) ≤ (a.2 + (h : ℤ) : ℝ) := by exact_mod_cast huBox.2.2
  have hvYlo : (a.2 : ℝ) ≤ (v.1.2 : ℝ) := by exact_mod_cast hvBox.2.1
  have hvYhi : (v.1.2 : ℝ) ≤ (a.2 + (h : ℤ) : ℝ) := by exact_mod_cast hvBox.2.2
  have hw0 : (0 : ℝ) ≤ (w : ℝ) := by positivity
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by positivity
  have hwCast : ((w : ℤ) : ℝ) = (w : ℝ) := by norm_num
  have hhCast : ((h : ℤ) : ℝ) = (h : ℝ) := by norm_num
  have hleftseg {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed exclusionMesh left)
      (latticeEmbed exclusionMesh u.1)) :
      ((a.1 : ℝ) - 1 ≤ z.re ∧ z.re ≤ ((a.1 + (w : ℤ) : ℝ) + 1) ∧
      (a.2 : ℝ) - 1 / 2 ≤ z.im ∧ z.im ≤ ((a.2 + (h : ℤ) : ℝ) + 1 / 2)) := by
    exact (exclusion_segment_coordinate_bounds
    (l := (a.1 : ℝ) - 1) (r := ((a.1 + (w : ℤ) : ℝ) + 1))
    (d := (a.2 : ℝ) - 1 / 2) (top := ((a.2 + (h : ℤ) : ℝ) + 1 / 2))
    (latticeEmbed exclusionMesh left) (latticeEmbed exclusionMesh u.1) hz
    (by simp [left,latticeEmbed,exclusionMesh])
    (by simp [latticeEmbed,exclusionMesh]; linarith [huX])
    (by simp [left,latticeEmbed,exclusionMesh]; linarith [hw0])
    (by simp [latticeEmbed,exclusionMesh]; linarith [huX, hw0])
    (by simp [left,latticeEmbed,exclusionMesh]; linarith [huYlo])
    (by simp [latticeEmbed,exclusionMesh]; linarith [huYlo])
    (by simp [left,latticeEmbed,exclusionMesh]; linarith [huYhi, hhCast])
    (by simp [latticeEmbed,exclusionMesh]; linarith [huYhi, hhCast]))
  have hrightseg {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed exclusionMesh v.1)
      (latticeEmbed exclusionMesh right)) :
      ((a.1 : ℝ) - 1 ≤ z.re ∧ z.re ≤ ((a.1 + (w : ℤ) : ℝ) + 1) ∧
      (a.2 : ℝ) - 1 / 2 ≤ z.im ∧ z.im ≤ ((a.2 + (h : ℤ) : ℝ) + 1 / 2)) := by
    exact (exclusion_segment_coordinate_bounds
    (l := (a.1 : ℝ) - 1) (r := ((a.1 + (w : ℤ) : ℝ) + 1))
    (d := (a.2 : ℝ) - 1 / 2) (top := ((a.2 + (h : ℤ) : ℝ) + 1 / 2))
    (latticeEmbed exclusionMesh v.1) (latticeEmbed exclusionMesh right) hz
    (by
      simp [latticeEmbed,exclusionMesh]
      have hb : (a.1 : ℝ) ≤ (v.1.1 : ℝ) := by exact_mod_cast hvBox.1.1
      linarith)
    (by simp [right,latticeEmbed,exclusionMesh]; linarith [hw0])
    (by
      simp [latticeEmbed,exclusionMesh]
      have hb : (v.1.1 : ℝ) ≤ (a.1 + (w : ℤ) : ℝ) := by exact_mod_cast hvBox.1.2
      linarith)
    (by simp [right,latticeEmbed,exclusionMesh])
    (by simp [latticeEmbed,exclusionMesh]; linarith [hvYlo])
    (by simp [right,latticeEmbed,exclusionMesh]; linarith [hvYlo])
    (by simp [latticeEmbed,exclusionMesh]; linarith [hvYhi, hhCast])
    (by simp [right,latticeEmbed,exclusionMesh]; linarith [hvYhi, hhCast]))
  have hP : rectangleExtendedPrimalWalkPath a w ps t ∈
      Set.range (rectangleExtendedPrimalWalkPath a w ps) := ⟨t,rfl⟩
  change rectangleExtendedPrimalWalkPath a w ps t ∈
    Set.range ((Path.segment (latticeEmbed exclusionMesh left)
        (latticeEmbed exclusionMesh (rectangleOpenGraphToSquare a w h A u))).trans
      ((latticeWalkPath exclusionMesh ps).trans
        (Path.segment (latticeEmbed exclusionMesh (rectangleOpenGraphToSquare a w h A v))
          (latticeEmbed exclusionMesh right)))) at hP
  rw [Path.trans_range] at hP
  rcases hP with hleft | hmidright
  · rw [Path.range_segment] at hleft
    exact hleftseg hleft
  · rw [Path.trans_range] at hmidright
    rcases hmidright with hmid | hright
    · rcases hmid with ⟨s,hs⟩
      have hb := rectangleOpenWalkPath_coordinates a w h A p s
      have hb' : (a.1 : ℝ) ≤ (rectangleExtendedPrimalWalkPath a w ps t).re ∧
          (rectangleExtendedPrimalWalkPath a w ps t).re ≤ ((a.1 + (w : ℤ) : ℝ)) ∧
          (a.2 : ℝ) ≤ (rectangleExtendedPrimalWalkPath a w ps t).im ∧
          (rectangleExtendedPrimalWalkPath a w ps t).im ≤ ((a.2 + (h : ℤ) : ℝ)) := by
        rw [← hs]
        simpa [rectangleExtendedPrimalWalkPath, ps, Path.trans_apply] using hb
      exact ⟨by linarith [hb'.1], by linarith [hb'.2.1],
        by linarith [hb'.2.2.1], by linarith [hb'.2.2.2]⟩
    · have hseg : rectangleExtendedPrimalWalkPath a w ps t ∈
        Set.range (Path.segment (latticeEmbed exclusionMesh
          (rectangleOpenGraphToSquare a w h A v)) (latticeEmbed exclusionMesh right)) := hright
      rw [Path.range_segment] at hseg
      exact hrightseg hseg

private theorem rectangleDualWalkPath_point_on_dualBond
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v)
    (hqpos : 0 < (q.map (rectangleDualOpenGraphToSquare a w h
      (rectangleDualConfiguration a w h A))).length)
    {z : ℂ} (hz : z ∈ Set.range (rectangleDualCenterWalkPath
      (q.map (rectangleDualOpenGraphToSquare a w h
        (rectangleDualConfiguration a w h A))))) :
    ∃ e : RectangleDualEdgeCarrier a w h,
      e.primalEdge ∉ A ∧ z ∈ dualBondSegment exclusionMesh e.crossingBond := by
  let qs := q.map (rectangleDualOpenGraphToSquare a w h
    (rectangleDualConfiguration a w h A))
  obtain ⟨x,y,hx,hy,hedge,hadj,hseg⟩ :=
    rectangleDualCenterWalkPath_range_actual_segment qs hqpos hz
  obtain ⟨e,heclosed,hpair⟩ :=
    rectangleDualWalk_segment_edge_label a w h A q hedge
  exact ⟨e,heclosed,dualCenterSegment_subset_label e.crossingBond hpair hseg⟩

private theorem rectanglePrimal_open_dual_closed_no_intersection
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (e : rectanglePrimalEdgeCarrier a w h) (he : e ∈ A)
    (d : RectangleDualEdgeCarrier a w h) (hd : d.primalEdge ∉ A)
    {z : ℂ} (hzP : z ∈ primalBondSegment exclusionMesh
      (rectanglePrimalEdgeBond a w h e))
    (hzD : z ∈ dualBondSegment exclusionMesh d.crossingBond) : False := by
  have hcross := (primalDualSegments_intersect_iff exclusionMesh
    (rectanglePrimalEdgeBond a w h e) d.crossingBond).mp ⟨z,hzP,hzD⟩
  have hbonds : rectanglePrimalEdgeBond a w h d.primalEdge =
      rectanglePrimalEdgeBond a w h e := by
    have h := congrArg primalBondOfDual hcross
    simpa only [rectangleDualEdge_crossedPrimalBond,
      primalBondOfDual_dualBondOfPrimal] using h
  have htoSym2 := congrArg LatticeBond.toSym2 hbonds
  have hsym : Sym2.map (fun x : RectangleVertex a w h => x.val) d.primalEdge.1 =
      Sym2.map (fun x : RectangleVertex a w h => x.val) e.1 := by
    simpa only [rectanglePrimalEdgeBond_toSym2_public] using htoSym2
  have heq : d.primalEdge = e := by
    apply Subtype.ext
    exact (Sym2.map.injective Subtype.val_injective) hsym
  subst e
  exact hd he

/-- An actual left-right open primal crossing and an actual bottom-top
complementary-dual crossing cannot coexist. The dual endpoints are on the true
expanded face-base rows; no boundary wiring is used. -/
theorem rectanglePrimalDualCrossings_exclusive
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (hP : A ∈ rectangleHorizontalCrossingEvent a w h)
    (hD : A ∈ rectangleComplementDualVerticalCrossingEvent a w h) : False := by
  rcases hP with ⟨u,v,hu,hv,hconnP⟩
  rcases hD with ⟨uD,vD,huD,hvD,hconnD⟩
  obtain ⟨p⟩ := (actualConnected_iff_walk (rectangleGraph a w h) A u v).mp hconnP
  obtain ⟨q⟩ := (actualConnected_iff_walk (rectangleDualGraph a w h)
    (rectangleDualConfiguration a w h A) uD vD).mp hconnD
  have hux : u.1.1 = a.1 := by
    exact (Finset.mem_filter.mp hu).2
  have hvx : v.1.1 = a.1 + (w : ℤ) := by
    exact (Finset.mem_filter.mp hv).2
  have hqneq : uD.1 ≠ vD.1 := by
    intro he
    have hy := congrArg Prod.snd he
    rw [huD, hvD] at hy
    omega
  have hqpos0 : 0 < q.length := by
    by_contra hn
    have hzero : q.length = 0 := by omega
    have heq := SimpleGraph.Walk.eq_of_length_eq_zero hzero
    exact hqneq (congrArg Subtype.val heq)
  let ps := p.map (rectangleOpenGraphToSquare a w h A)
  let qs := q.map (rectangleDualOpenGraphToSquare a w h
    (rectangleDualConfiguration a w h A))
  have hqpos : 0 < qs.length := by simpa [qs] using hqpos0
  let pc := rectangleExtendedPrimalWalkPath a w ps
  let qc := rectangleDualCenterWalkPath qs
  let P := pc.map continuous_exclusionComplexToPair
  let Q := qc.map continuous_exclusionComplexToPair
  let left : ℝ := (a.1 : ℝ) - 1
  let right : ℝ := ((a.1 + (w : ℤ) : ℝ) + 1)
  let bottom : ℝ := (a.2 : ℝ) - 1 / 2
  let top : ℝ := ((a.2 + (h : ℤ) : ℝ) + 1 / 2)
  have hwCast : ((w : ℤ) : ℝ) = (w : ℝ) := by norm_num
  have hhCast : ((h : ℤ) : ℝ) = (h : ℝ) := by norm_num
  have hleftle : left ≤ right := by
    dsimp [left,right]
    have hw : (0:ℝ) ≤ (w : ℝ) := by positivity
    rw [hwCast]
    linarith
  have hbottomle : bottom ≤ top := by
    dsimp [bottom,top]
    have hh : (0:ℝ) ≤ (h : ℝ) := by positivity
    rw [hhCast]
    linarith
  have hPbox : ∀ t, left ≤ (P t).1 ∧ (P t).1 ≤ right ∧
      bottom ≤ (P t).2 ∧ (P t).2 ≤ top := by
    intro t
    have hb := rectangleExtendedPrimalWalkPath_coordinates a w h A p hux hvx t
    change left ≤ (pc t).re ∧ (pc t).re ≤ right ∧
      bottom ≤ (pc t).im ∧ (pc t).im ≤ top
    simpa [left, right, bottom, top] using hb
  have hQbox : ∀ t, left ≤ (Q t).1 ∧ (Q t).1 ≤ right ∧
      bottom ≤ (Q t).2 ∧ (Q t).2 ≤ top := by
    intro t
    have hb := rectangleDualCenterWalkPath_coordinates a w h A q hqpos t
    rcases hb with ⟨hxl,hxu,hyl,hyu⟩
    change left ≤ (qc t).re ∧ (qc t).re ≤ right ∧
      bottom ≤ (qc t).im ∧ (qc t).im ≤ top
    exact ⟨by dsimp [left]; linarith, by dsimp [right]; linarith,
      by dsimp [bottom]; linarith, by dsimp [top]; linarith⟩
  have hPleft : (P 0).1 = left := by
    have hs := congrArg Prod.fst P.source'
    simpa [left, exclusionComplexToPair, latticeEmbed, exclusionMesh] using hs
  have hPright : (P 1).1 = right := by
    have ht := congrArg Prod.fst P.target'
    simpa [right, exclusionComplexToPair, latticeEmbed, exclusionMesh, hvx] using ht
  have hQbottom : (Q 0).2 = bottom := by
    have hs := congrArg Prod.snd Q.source'
    have hs' : (Q 0).2 = (uD.1.2 : ℝ) + 1 / 2 := by
      simpa [dualFaceCenter, exclusionComplexToPair, latticeEmbed,
        exclusionMesh, exclusionOffset, rectangleDualOpenGraphToSquare] using hs
    rw [hs', huD]
    dsimp [bottom]
    push_cast
    norm_num
    ring
  have hQtop : (Q 1).2 = top := by
    have ht := congrArg Prod.snd Q.target'
    have ht' : (Q 1).2 = (vD.1.2 : ℝ) + 1 / 2 := by
      simpa [dualFaceCenter, exclusionComplexToPair, latticeEmbed,
        exclusionMesh, exclusionOffset, rectangleDualOpenGraphToSquare] using ht
    rw [ht', hvD]
    dsimp [top]
    push_cast
    ring
  obtain ⟨s,t,hst⟩ := pathRectangle_crossing_intersection
    (a := (left,bottom)) (b := (right,top)) P Q
    hPbox hQbox hPleft hPright hQbottom hQtop
  have hcomplex : pc s = qc t := by
    apply Complex.ext
    · exact congrArg Prod.fst hst
    · exact congrArg Prod.snd hst
  let z := qc t
  have hzDual : z ∈ Set.range qc := ⟨t,rfl⟩
  obtain ⟨d,hdclosed,hzD⟩ := rectangleDualWalkPath_point_on_dualBond
    a w h A q hqpos hzDual
  have hzPrimal : z ∈ Set.range pc := ⟨s,by simpa [z] using hcomplex⟩
  change z ∈ Set.range (rectangleExtendedPrimalWalkPath a w ps) at hzPrimal
  unfold rectangleExtendedPrimalWalkPath at hzPrimal
  rw [Path.trans_range] at hzPrimal
  rcases hzPrimal with hleftSeg | hmiddleRight
  · rw [Path.range_segment] at hleftSeg
    let bLeft : LatticeBond := ⟨(a.1 - 1,u.1.2), .horizontal⟩
    have hzLeft : z ∈ primalBondSegment exclusionMesh bLeft := by
      rw [primalBondSegment, LatticeBond.source, LatticeBond.target]
      simpa [bLeft, LatticeBond.source, LatticeBond.target, latticeEmbed,
        rectangleOpenGraphToSquare, exclusionMesh, hux] using hleftSeg
    have hcross := (primalDualSegments_intersect_iff exclusionMesh bLeft
      d.crossingBond).mp ⟨z,hzLeft,hzD⟩
    have hbonds : rectanglePrimalEdgeBond a w h d.primalEdge = bLeft := by
      have hh := congrArg primalBondOfDual hcross
      simpa only [rectangleDualEdge_crossedPrimalBond,
        primalBondOfDual_dualBondOfPrimal] using hh
    have hsrc := (rectanglePrimalEdgeBond_endpoints_mem_public a w h d.primalEdge).1
    rw [hbonds] at hsrc
    have hnot : bLeft.source ∉ latticeRectangle a w h := by
      intro hm
      have hm' := (mem_latticeRectangle a bLeft.source w h).mp hm
      simp [bLeft, LatticeBond.source] at hm'
    exact False.elim (hnot hsrc)
  · rw [Path.trans_range] at hmiddleRight
    rcases hmiddleRight with hmiddle | hrightSeg
    · by_cases hlen : ps.length = 0
      · have hzvertex : z = latticeEmbed exclusionMesh u.1 := by
          have heq := SimpleGraph.Walk.eq_of_length_eq_zero hlen
          have huv : u = v := Subtype.ext heq
          subst v
          have hnil : ps.Nil := SimpleGraph.Walk.length_eq_zero_iff.mp hlen
          have hps : ps = .nil := hnil.eq_nil
          have hpath : latticeWalkPath exclusionMesh ps =
              Path.refl (latticeEmbed exclusionMesh
                ((rectangleOpenGraphToSquare a w h A) u)) := by
            rw [hps]
            rfl
          rw [hpath, Path.refl_range] at hmiddle
          simpa [rectangleOpenGraphToSquare] using hmiddle
        exact (rectangleDualCenterWalkPath_avoids_vertex a w h A q u.1 t) hzvertex
      · have hposP : 0 < ps.length := by omega
        obtain ⟨x,y,hx,hy,hedge,hadj,hseg⟩ :=
          latticeWalkPath_range_actual_segment ps hposP hmiddle
        obtain ⟨e,heopen,hpair⟩ := rectanglePrimalWalk_segment_edge_label a w h A p hedge
        have hzP : z ∈ primalBondSegment exclusionMesh (rectanglePrimalEdgeBond a w h e) :=
          latticeSegment_subset_primalBond (rectanglePrimalEdgeBond a w h e) hpair hseg
        exact rectanglePrimal_open_dual_closed_no_intersection a w h A e heopen d hdclosed hzP hzD
    · rw [Path.range_segment] at hrightSeg
      let bRight : LatticeBond := ⟨v.1, .horizontal⟩
      have hzRight : z ∈ primalBondSegment exclusionMesh bRight := by
        rw [primalBondSegment, LatticeBond.source, LatticeBond.target]
        simpa [bRight, LatticeBond.source, LatticeBond.target, latticeEmbed,
          rectangleOpenGraphToSquare,
          exclusionMesh, hvx] using hrightSeg
      have hcross := (primalDualSegments_intersect_iff exclusionMesh bRight
        d.crossingBond).mp ⟨z,hzRight,hzD⟩
      have hbonds : rectanglePrimalEdgeBond a w h d.primalEdge = bRight := by
        have hh := congrArg primalBondOfDual hcross
        simpa only [rectangleDualEdge_crossedPrimalBond,
          primalBondOfDual_dualBondOfPrimal] using hh
      have htgt := (rectanglePrimalEdgeBond_endpoints_mem_public a w h d.primalEdge).2
      rw [hbonds] at htgt
      have hnot : bRight.target ∉ latticeRectangle a w h := by
        intro hm
        have hm' := (mem_latticeRectangle a bRight.target w h).mp hm
        simp [bRight, LatticeBond.target, hvx] at hm'
      exact False.elim (hnot htgt)
end
end PottsDiscontinuity.FK
