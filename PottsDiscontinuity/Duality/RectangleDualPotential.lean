/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleCurlLinearEquiv
public import PottsDiscontinuity.Duality.RectangleFlowDimension
public import PottsDiscontinuity.Duality.NormalizedPotentialSpace

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable def rectangleDualConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleDualGraph a w h) :=
  Finset.map (rectangleDualGraphEdgeEquiv a w h).toEmbedding
    (rectangleDualComplementEquiv a w h A)

@[simp] theorem mem_rectangleDualConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h e ∈ rectangleDualConfiguration a w h A ↔
      e.primalEdge ∉ A := by
  classical
  simp [rectangleDualConfiguration,
    mem_rectangleDualComplementEquiv]

private theorem mem_rectangleDualConfiguration_iff
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (g : (rectangleDualGraph a w h).edgeSet) :
    g ∈ rectangleDualConfiguration a w h A ↔
      ((rectangleDualGraphEdgeEquiv a w h).symm g).primalEdge ∉ A := by
  classical
  constructor
  · intro hg
    rcases Finset.mem_map.mp hg with ⟨e, he, hge⟩
    have hback := congrArg (fun x => (rectangleDualGraphEdgeEquiv a w h).symm x) hge
    have heq : (rectangleDualGraphEdgeEquiv a w h).symm g = e := by
      simpa using hback.symm
    rw [heq]
    exact (mem_rectangleDualComplementEquiv a w h A e).mp he
  · intro hg
    apply Finset.mem_map.mpr
    refine ⟨(rectangleDualGraphEdgeEquiv a w h).symm g, ?_, ?_⟩
    · exact (mem_rectangleDualComplementEquiv a w h A _).mpr hg
    · exact Equiv.apply_symm_apply _ _

private theorem rectangleDualOpen_adj_iff
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (u v : RectangleDualVertex a w h) :
    (openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A)).Adj u v ↔
      ∃ e : RectangleDualEdgeCarrier a w h,
        e.primalEdge ∉ A ∧ s(u,v) = rectangleDualCarrierPair a w h e := by
  rw [openGraph_adj, openEdges]
  constructor
  · intro hv
    change ∃ g : (rectangleDualGraph a w h).edgeSet,
      g ∈ rectangleDualConfiguration a w h A ∧ (g : Sym2 _) = s(u,v) at hv
    rcases hv with ⟨g, hg, hgv⟩
    let e := (rectangleDualGraphEdgeEquiv a w h).symm g
    refine ⟨e, ?_, ?_⟩
    · exact (mem_rectangleDualConfiguration_iff a w h A g).mp hg
    · have he : rectangleDualGraphEdgeEquiv a w h e = g := Equiv.apply_symm_apply _ _
      have hval := congrArg Subtype.val he
      have hpair : (rectangleDualGraphEdgeEquiv a w h e : Sym2 _) =
          rectangleDualCarrierPair a w h e := by
        rfl
      exact hgv.symm.trans (hval.symm.trans hpair)
  · rintro ⟨e, he, huv⟩
    change ∃ g : (rectangleDualGraph a w h).edgeSet,
      g ∈ rectangleDualConfiguration a w h A ∧ (g : Sym2 _) = s(u,v)
    refine ⟨rectangleDualGraphEdgeEquiv a w h e, ?_, ?_⟩
    · exact (mem_rectangleDualConfiguration a w h A e).mpr he
    · change rectangleDualCarrierPair a w h e = s(u,v)
      exact huv.symm

def rectangleDualBaseVertex (a : LatticeVertex) (w h : ℕ) :
    RectangleDualVertex a w h :=
  ⟨(a.1 - 1, a.2 - 1), by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    simp
    omega⟩

theorem rectangleDualBaseVertex_boundary (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualBaseVertex a w h).1 ∈ rectangleDualBoundary a w h := by
  simp [rectangleDualBaseVertex, rectangleDualBoundary, rectangleDualInterior,
    rectangleDualExpanded, mem_latticeRectangle, Finset.mem_filter]
  omega

noncomputable def rectanglePrimalEdgeBond_mem (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) : RectanglePrimalBond a w h :=
  ⟨rectanglePrimalEdgeBond a w h e,
    rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩

private def rectanglePotentialAsExterior (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) : RectangleExteriorPotential a w h :=
  ⟨φ.1, φ.2⟩

def rectangleDualPotentialExtended (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h) (z : LatticeVertex) : ℝ :=
  if hz : z ∈ rectangleDualExpanded a w h then φ.1 ⟨z, hz⟩ else 0

/-- Zero-exterior potentials whose curl vanishes on every closed primal edge
(the complement of the open primal configuration A). -/
def rectangleDualPotentialCurlKernel (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Submodule ℝ (rectangleExteriorPotentialSubmodule a w h) where
  carrier := {φ | ∀ e : rectanglePrimalEdgeCarrier a w h, e ∉ A →
    rectanglePotentialCurlMap a w h φ (rectanglePrimalEdgeBond_mem a w h e) = 0}
  zero_mem' := by
    intro φ
    simp
  add_mem' := by
    intro φ ψ hφ hψ e he
    rw [map_add]
    simp [hφ e he, hψ e he]
  smul_mem' := by
    intro c φ hφ e he
    rw [map_smul]
    simp [hφ e he]

private theorem rectanglePotentialCurl_zero_iff_dualEnds_eq
    (a : LatticeVertex) (w h : ℕ)
    (φ : rectangleExteriorPotentialSubmodule a w h)
    (e : rectanglePrimalEdgeCarrier a w h) :
    rectanglePotentialCurlMap a w h φ (rectanglePrimalEdgeBond_mem a w h e) = 0 ↔
      φ.1 (rectangleDualEdgeSource a w h
        (rectanglePrimalDualEdgeEquiv a w h e)) =
      φ.1 (rectangleDualEdgeTarget a w h
        (rectanglePrimalDualEdgeEquiv a w h e)) := by
  let d := rectanglePrimalDualEdgeEquiv a w h e
  let b := rectanglePrimalEdgeBond a w h e
  have hsrc : d.primalEdge = e := by rfl
  have hs : (rectangleDualEdgeSource a w h d).val = b.faceBase false := by
    simpa [d, hsrc, b] using rectangleDualEdgeSource_faceBase a w h d
  have ht : (rectangleDualEdgeTarget a w h d).val = b.faceBase true := by
    simpa [d, hsrc, b] using rectangleDualEdgeTarget_faceBase a w h d
  have hsource : rectangleExtendedPotential a w h
      (rectanglePotentialAsExterior a w h φ) (b.faceBase false) =
      rectangleDualPotentialExtended a w h φ (rectangleDualEdgeSource a w h d).val := by
    rw [← hs]
    rfl
  have htarget : rectangleExtendedPotential a w h
      (rectanglePotentialAsExterior a w h φ) (b.faceBase true) =
      rectangleDualPotentialExtended a w h φ (rectangleDualEdgeTarget a w h d).val := by
    rw [← ht]
    rfl
  have hsrcval : rectangleDualPotentialExtended a w h φ
      (rectangleDualEdgeSource a w h d).val = φ.1 (rectangleDualEdgeSource a w h d) := by
    change (if hz : (rectangleDualEdgeSource a w h d).val ∈ rectangleDualExpanded a w h
      then φ.1 ⟨(rectangleDualEdgeSource a w h d).val, hz⟩ else 0) = _
    rw [dite_eq_left (rectangleDualEdgeSource a w h d).property]
  have htgtval : rectangleDualPotentialExtended a w h φ
      (rectangleDualEdgeTarget a w h d).val = φ.1 (rectangleDualEdgeTarget a w h d) := by
    change (if hz : (rectangleDualEdgeTarget a w h d).val ∈ rectangleDualExpanded a w h
      then φ.1 ⟨(rectangleDualEdgeTarget a w h d).val, hz⟩ else 0) = _
    rw [dite_eq_left (rectangleDualEdgeTarget a w h d).property]
  change rectangleCurlFlow a w h (rectanglePotentialAsExterior a w h φ) b = 0 ↔ _
  cases haxis : b.axis
  · simp only [rectangleCurlFlow, haxis]
    rw [hsource, htarget, hsrcval, htgtval]
    constructor
    · intro hz
      exact sub_eq_zero.mp hz |>.symm
    · intro heq
      exact sub_eq_zero.mpr heq.symm
  · simp only [rectangleCurlFlow, haxis]
    rw [hsource, htarget, hsrcval, htgtval]
    exact sub_eq_zero

noncomputable abbrev RectangleDualNormalizedPotentials (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :=
  normalizedComponentPotentials (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h)
    (rectangleDualConfiguration a w h A) (rectangleDualBaseVertex a w h)

private theorem rectangleDualNormalized_boundary_zero
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (f : RectangleDualNormalizedPotentials a w h A) (z : RectangleDualVertex a w h)
    (hz : z.1 ∈ rectangleDualBoundary a w h) : f.1.1 z = 0 := by
  have hrel : (rectangleDualBoundaryCondition a w h).partition.r z
      (rectangleDualBaseVertex a w h) := by
    rw [rectangleDualBoundaryCondition_rel]
    exact Or.inr ⟨hz, rectangleDualBaseVertex_boundary a w h⟩
  have hcomp := boundary_component (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h) (rectangleDualConfiguration a w h A) hrel
  have heq := f.1.2 hcomp
  have hnorm : f.1.1 (rectangleDualBaseVertex a w h) = 0 := by
    have hm := f.2
    change f.1 ∈ LinearMap.ker
      (componentPotentialEvaluation (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h A)
        (rectangleDualBaseVertex a w h)) at hm
    rw [LinearMap.mem_ker] at hm
    simpa [componentPotentialEvaluation] using hm
  exact heq.trans hnorm

 theorem rectangleDualNormalized_mem_exterior
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (f : RectangleDualNormalizedPotentials a w h A) :
    f.1.1 ∈ rectangleExteriorPotentialSubmodule a w h := by
  change ∀ z : RectangleDualVertex a w h, z.1 ∈ rectangleDualBoundary a w h → f.1.1 z = 0
  intro z hz
  exact rectangleDualNormalized_boundary_zero a w h A f z hz

 theorem rectangleDualNormalized_mem_curlKernel
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (f : RectangleDualNormalizedPotentials a w h A) :
    (⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩ :
      rectangleExteriorPotentialSubmodule a w h) ∈ rectangleDualPotentialCurlKernel a w h A := by
  intro e he
  let d := rectanglePrimalDualEdgeEquiv a w h e
  have hAdj : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Adj
      (rectangleDualEdgeSource a w h d) (rectangleDualEdgeTarget a w h d) := by
    apply (rectangleDualOpen_adj_iff a w h A _ _).2
    refine ⟨d, ?_, ?_⟩
    · simpa [d, rectanglePrimalDualEdgeEquiv] using he
    · rfl
  have hlocal := (componentConstant_iff_local (rectangleDualGraph a w h)
    (rectangleDualBoundaryCondition a w h)
    (rectangleDualConfiguration a w h A) f.1.1).mp f.1.2
  have heq := hlocal.1 hAdj
  exact (rectanglePotentialCurl_zero_iff_dualEnds_eq a w h
    ⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩ e).2 heq

/-- The normalized wired dual potentials embed as zero-exterior potentials
whose curl vanishes on every closed primal edge. -/
def rectangleDualNormalizedToCurlKernel (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    RectangleDualNormalizedPotentials a w h A →ₗ[ℝ]
      rectangleDualPotentialCurlKernel a w h A where
  toFun f := ⟨⟨f.1.1, rectangleDualNormalized_mem_exterior a w h A f⟩,
    rectangleDualNormalized_mem_curlKernel a w h A f⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem rectangleDualCurlKernel_local
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (φ : rectangleDualPotentialCurlKernel a w h A) :
    componentPotentialLocalPredicate (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration a w h A) φ.1.1 := by
  constructor
  · intro u v hadj
    rcases (rectangleDualOpen_adj_iff a w h A u v).mp hadj with ⟨e, he, huv⟩
    let de := rectanglePrimalDualEdgeEquiv a w h e.primalEdge
    have hde : de = e := by
      exact (rectanglePrimalDualEdgeEquiv a w h).right_inv e
    have hpair : s(u,v) = rectangleDualCarrierPair a w h e := by
      simpa [de, hde] using huv
    have hp := (rectanglePotentialCurl_zero_iff_dualEnds_eq a w h φ.1 e.primalEdge).mp
      (φ.2 e.primalEdge he)
    rw [rectangleDualCarrierPair, Sym2.eq_iff] at hpair
    rcases hpair with hpair | hpair
    · have hu : u = rectangleDualEdgeSource a w h e := hpair.1
      have hv : v = rectangleDualEdgeTarget a w h e := hpair.2
      rw [← hde] at hu hv
      exact (congrArg φ.1.1 hu).trans (hp.trans (congrArg φ.1.1 hv).symm)
    · have hv : v = rectangleDualEdgeSource a w h e := hpair.2
      have hu : u = rectangleDualEdgeTarget a w h e := hpair.1
      rw [← hde] at hu hv
      exact (congrArg φ.1.1 hu).trans (hp.symm.trans (congrArg φ.1.1 hv).symm)
  · intro u v hrel
    have hrel' := (rectangleDualBoundaryCondition_rel a w h u v).mp hrel
    rcases hrel' with huv | ⟨hu,hv⟩
    · cases huv
      rfl
    · have hzu := φ.1.2 ⟨u.1, u.2⟩ hu
      have hzv := φ.1.2 ⟨v.1, v.2⟩ hv
      exact hzu.trans hzv.symm

 theorem rectangleDualCurlKernel_mem_componentConstant
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (φ : rectangleDualPotentialCurlKernel a w h A) :
    φ.1.1 ∈ componentConstantFunctions (rectangleDualGraph a w h)
      (rectangleDualBoundaryCondition a w h)
      (rectangleDualConfiguration a w h A) := by
  exact (componentConstant_iff_local _ _ _ _).mpr
    (rectangleDualCurlKernel_local a w h A φ)

 theorem rectangleDualCurlKernel_base_zero
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (φ : rectangleDualPotentialCurlKernel a w h A) :
    φ.1.1 (rectangleDualBaseVertex a w h) = 0 := by
  have hb := rectangleDualBaseVertex_boundary a w h
  exact φ.1.2 ⟨rectangleDualBaseVertex a w h,
    (rectangleDualBaseVertex a w h).property⟩ hb

def rectangleDualCurlKernelToNormalized (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualPotentialCurlKernel a w h A →ₗ[ℝ]
      RectangleDualNormalizedPotentials a w h A where
  toFun φ :=
    ⟨⟨φ.1.1, rectangleDualCurlKernel_mem_componentConstant a w h A φ⟩,
      rectangleDualCurlKernel_base_zero a w h A φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c φ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def rectangleDualPotentialNormalizedLinearEquiv
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    RectangleDualNormalizedPotentials a w h A ≃ₗ[ℝ]
      rectangleDualPotentialCurlKernel a w h A := by
  let f := rectangleDualNormalizedToCurlKernel a w h A
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : rectangleDualPotentialCurlKernel a w h A => z.1.1) hxy
  · intro φ
    refine ⟨rectangleDualCurlKernelToNormalized a w h A φ, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

 theorem rectangleDualPotentialCurlKernel_finrank_add_one
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Module.finrank ℝ (rectangleDualPotentialCurlKernel a w h A) + 1 =
      componentCount (rectangleDualGraph a w h)
        (rectangleDualBoundaryCondition a w h)
        (rectangleDualConfiguration a w h A) := by
  have heq := (rectangleDualPotentialNormalizedLinearEquiv a w h A).finrank_eq
  rw [← heq]
  exact normalizedComponentPotentials_finrank_add_one _ _ _ _

end PottsDiscontinuity.FK
