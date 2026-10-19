/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleCurlLinearEquiv
public import PottsDiscontinuity.Duality.RectangleFlowDimension

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

variable (a : LatticeVertex) (w h : ℕ)
variable (A : Configuration (rectangleGraph a w h))

local instance rectangleOpenIndexFintype :
    Fintype (OpenEdgeIndex (rectangleGraph a w h) A) := Fintype.ofFinite _
local instance rectangleOpenIndexDecidableEq :
    DecidableEq (OpenEdgeIndex (rectangleGraph a w h) A) := Classical.decEq _

local instance rectangleOpenFlowCarrierFintype :
    Fintype (rectanglePrimalEdgeCarrier a w h) := by
  classical
  letI : Fintype (RectangleVertex a w h) := Fintype.ofFinite _
  letI : Fintype (Sym2 (RectangleVertex a w h)) := inferInstance
  letI : Finite (rectanglePrimalEdgeCarrier a w h) :=
    Finite.of_injective (fun e : rectanglePrimalEdgeCarrier a w h => e.1)
      Subtype.val_injective
  exact Fintype.ofFinite _

local instance rectangleOpenFlowBondFintype :
    Fintype (RectanglePrimalBond a w h) :=
  Fintype.ofEquiv (rectanglePrimalEdgeCarrier a w h)
    (rectanglePrimalEdgeBondEquiv a w h)

def rectangleBondToGraphEdge (b : RectanglePrimalBond a w h) :
    (rectangleGraph a w h).edgeSet := rectanglePrimalBondToEdge a w h b

/-- Extend an open-edge flow by zero to every normalized primal bond of the
rectangle. The selected-edge equivalence keeps the original unordered edge. -/
noncomputable def rectangleOpenFlowZeroExtend
    (f : OpenEdgeIndex (rectangleGraph a w h) A → ℝ) : RectanglePrimalFlow a w h := by
  classical
  exact fun b =>
    let e := rectangleBondToGraphEdge a w h b
    if hb : e ∈ A then f ⟨e, hb⟩ else 0

@[simp] theorem rectangleOpenFlowZeroExtend_onOpen
    (f : OpenEdgeIndex (rectangleGraph a w h) A → ℝ)
    (e : OpenEdgeIndex (rectangleGraph a w h) A) :
    rectangleOpenFlowZeroExtend a w h A f ((rectanglePrimalEdgeBondEquiv a w h) e.1) = f e := by
  classical
  have he : rectangleBondToGraphEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e.1) = e.1 := by
    change rectanglePrimalBondToEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e.1) = e.1
    exact (rectanglePrimalEdgeBondEquiv a w h).left_inv e.1
  unfold rectangleOpenFlowZeroExtend
  change (if hb : rectangleBondToGraphEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e.1) ∈ A then
        f ⟨rectangleBondToGraphEdge a w h
          ((rectanglePrimalEdgeBondEquiv a w h) e.1), hb⟩ else 0) = f e
  rw [he]
  simp



theorem rectangleOpenFlowZeroExtend_onClosed
    (f : OpenEdgeIndex (rectangleGraph a w h) A → ℝ)
    (b : RectanglePrimalBond a w h)
    (hb : rectangleBondToGraphEdge a w h b ∉ A) :
    rectangleOpenFlowZeroExtend a w h A f b = 0 := by
  classical
  unfold rectangleOpenFlowZeroExtend
  change (if h : rectangleBondToGraphEdge a w h b ∈ A then _ else 0) = 0
  simp [hb]


/-- The full-bond flow subspace supported on actual selected open rectangle edges. -/
def rectangleOpenFlowSubmodule : Submodule ℝ (RectanglePrimalFlow a w h) where
  carrier := {F | ∀ b : RectanglePrimalBond a w h,
    rectangleBondToGraphEdge a w h b ∉ A → F b = 0}
  zero_mem' := by simp
  add_mem' := by
    intro F H hF hH b hb
    simp [hF b hb, hH b hb]
  smul_mem' := by
    intro c F hF b hb
    simp [hF b hb]

/-- Zero extension is linear in the values on the actual open-edge set. -/
def rectangleOpenFlowZeroExtendLinear :
    (OpenEdgeIndex (rectangleGraph a w h) A → ℝ) →ₗ[ℝ] RectanglePrimalFlow a w h where
  toFun := rectangleOpenFlowZeroExtend a w h A
  map_add' f g := by
    classical
    funext b
    change (if hb : rectangleBondToGraphEdge a w h b ∈ A then
      f ⟨rectangleBondToGraphEdge a w h b, hb⟩ +
        g ⟨rectangleBondToGraphEdge a w h b, hb⟩ else 0) =
      (if hb : rectangleBondToGraphEdge a w h b ∈ A then
        f ⟨rectangleBondToGraphEdge a w h b, hb⟩ else 0) +
      (if hb : rectangleBondToGraphEdge a w h b ∈ A then
        g ⟨rectangleBondToGraphEdge a w h b, hb⟩ else 0)
    by_cases hb : rectangleBondToGraphEdge a w h b ∈ A <;> simp [hb]
  map_smul' c f := by
    classical
    funext b
    change (if hb : rectangleBondToGraphEdge a w h b ∈ A then
      c * f ⟨rectangleBondToGraphEdge a w h b, hb⟩ else 0) =
      c * (if hb : rectangleBondToGraphEdge a w h b ∈ A then
        f ⟨rectangleBondToGraphEdge a w h b, hb⟩ else 0)
    by_cases hb : rectangleBondToGraphEdge a w h b ∈ A <;> simp [hb]



/-- The zero-extension map identifies open-edge flows with full-bond flows
which vanish exactly on bonds outside the selected open edge set. -/
noncomputable def rectangleOpenFlowZeroExtendEquiv :
    (OpenEdgeIndex (rectangleGraph a w h) A → ℝ) ≃ₗ[ℝ]
      rectangleOpenFlowSubmodule a w h A where
  toFun f := ⟨rectangleOpenFlowZeroExtend a w h A f, by
    intro b hb
    exact rectangleOpenFlowZeroExtend_onClosed a w h A f b hb⟩
  invFun F e := F.1 ((rectanglePrimalEdgeBondEquiv a w h)
    (e.1 : rectanglePrimalEdgeCarrier a w h))
  left_inv f := by
    funext e
    simp
  right_inv F := by
    apply Subtype.ext
    funext b
    change (if hb : rectangleBondToGraphEdge a w h b ∈ A then
      F.1 ((rectanglePrimalEdgeBondEquiv a w h)
        (rectangleBondToGraphEdge a w h b)) else 0) = F.1 b
    split_ifs with hb
    · have hbond : (rectanglePrimalEdgeBondEquiv a w h)
          (rectanglePrimalBondToEdge a w h b) = b :=
        Equiv.apply_symm_apply _ _
      simpa [rectangleBondToGraphEdge] using congrArg F.1 hbond
    · simpa using (F.2 b hb).symm
  map_add' f g := by
    apply Subtype.ext
    exact map_add (rectangleOpenFlowZeroExtendLinear a w h A) f g
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (rectangleOpenFlowZeroExtendLinear a w h A) c f




def rectangleOpenBondIndex :=
  {b : RectanglePrimalBond a w h // rectangleBondToGraphEdge a w h b ∈ A}

local instance rectangleOpenBondIndexFinite :
    Finite (rectangleOpenBondIndex a w h A) := by
  classical
  let : Fintype (RectanglePrimalBond a w h) := rectangleOpenFlowBondFintype a w h
  exact Finite.of_injective Subtype.val Subtype.val_injective
local instance rectangleOpenBondIndexFintype :
    Fintype (rectangleOpenBondIndex a w h A) := Fintype.ofFinite _

noncomputable def rectangleOpenBondEquiv :
    OpenEdgeIndex (rectangleGraph a w h) A ≃ rectangleOpenBondIndex a w h A where
  toFun e := by
    let b : RectanglePrimalBond a w h :=
      (rectanglePrimalEdgeBondEquiv a w h) e.1
    have hEdge : rectangleBondToGraphEdge a w h b = e.1 := by
      change (rectanglePrimalEdgeBondEquiv a w h).symm b = e.1
      rw [show b = (rectanglePrimalEdgeBondEquiv a w h) e.1 by rfl]
      exact (rectanglePrimalEdgeBondEquiv a w h).left_inv e.1
    exact ⟨b, by rw [hEdge]; exact e.2⟩
  invFun b := ⟨rectangleBondToGraphEdge a w h b.1, b.2⟩
  left_inv e := by
    apply Subtype.ext
    change rectangleBondToGraphEdge a w h
      ((rectanglePrimalEdgeBondEquiv a w h) e.1) = e.1
    change (rectanglePrimalEdgeBondEquiv a w h).symm
      ((rectanglePrimalEdgeBondEquiv a w h) e.1) = e.1
    exact (rectanglePrimalEdgeBondEquiv a w h).left_inv e.1
  right_inv b := by
    apply Subtype.ext
    change (rectanglePrimalEdgeBondEquiv a w h)
      (rectanglePrimalBondToEdge a w h b.1) = b.1
    exact Equiv.apply_symm_apply _ _


def rectangleBondSignedTerm (F : RectanglePrimalFlow a w h)
    (v : LatticeVertex) (b : RectanglePrimalBond a w h) : ℝ :=
  (if b.1.source = v then F b else 0) -
    (if b.1.target = v then F b else 0)

theorem rectanglePrimalFlowDivergence_eq_allBonds
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h F v =
      ∑ b : RectanglePrimalBond a w h, rectangleBondSignedTerm a w h F v b := by
  classical
  let p : RectanglePrimalBond a w h → Prop :=
    fun b => b.1.source = v ∨ b.1.target = v
  let T := rectangleBondSignedTerm a w h F v
  have hterm (b : rectangleActualIncidentBonds a w h v) :
      (if b.1.1.source = v then F b.1 else -F b.1) = T b.1 := by
    rcases b.2 with hs | ht
    · have hne : b.1.1.target ≠ v := by
        intro h
        exact b.1.1.source_ne_target (hs.trans h.symm)
      simp [T, rectangleBondSignedTerm, hs, hne]
    · have hne : b.1.1.source ≠ v := by
        intro h
        exact b.1.1.source_ne_target (h.trans ht.symm)
      simp [T, rectangleBondSignedTerm, hne, ht]
  let incidentEquiv : rectangleActualIncidentBonds a w h v ≃
      {b : RectanglePrimalBond a w h // p b} := {
    toFun := fun b => ⟨b.1, by simpa [p] using b.2⟩
    invFun := fun b => ⟨b.1, by simpa [p] using b.2⟩
    left_inv := by intro b; apply Subtype.ext; rfl
    right_inv := by intro b; apply Subtype.ext; rfl }
  have hsub :
      (∑ b ∈ Finset.univ.filter p, T b) =
        ∑ b : {b : RectanglePrimalBond a w h // p b}, T b.1 :=
    Finset.sum_subtype (p := p) (Finset.univ.filter p)
      (by intro b; simp [p]) T
  have hzero (b : RectanglePrimalBond a w h) (hb : ¬ p b) : T b = 0 := by
    have hs : b.1.source ≠ v := by intro h; exact hb (Or.inl h)
    have ht : b.1.target ≠ v := by intro h; exact hb (Or.inr h)
    simp [T, rectangleBondSignedTerm, hs, ht]
  calc
    rectanglePrimalFlowDivergence a w h F v =
        ∑ b : rectangleActualIncidentBonds a w h v, T b.1 := by
      unfold rectanglePrimalFlowDivergence
      apply Finset.sum_congr rfl
      intro b hb
      exact hterm b
    _ = ∑ b : {b : RectanglePrimalBond a w h // p b}, T b.1 := by
      exact Equiv.sum_comp incidentEquiv (fun b => T b.1)
    _ = ∑ b ∈ Finset.univ.filter p, T b := hsub.symm
    _ = ∑ b : RectanglePrimalBond a w h, T b := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hp : p b
      · simp [p, hp]
      · have hz := hzero b hp
        simp [p, hp, hz]


theorem rectangleOpenFlowZeroExtend_signedDivergence
    (f : OpenEdgeIndex (rectangleGraph a w h) A → ℝ)
    (v : RectangleVertex a w h) :
    signedDivergence (rectangleGraph a w h) A
      (rectangleOpenEdgeOrientation a w h A) f v =
      rectanglePrimalFlowDivergence a w h
        (rectangleOpenFlowZeroExtend a w h A f) v.1 := by
  classical
  let F := rectangleOpenFlowZeroExtend a w h A f
  let q : RectanglePrimalBond a w h → Prop :=
    fun b => rectangleBondToGraphEdge a w h b ∈ A
  let : DecidablePred q := Classical.decPred q
  let : Fintype (RectanglePrimalBond a w h) := rectangleOpenFlowBondFintype a w h
  let : Fintype (rectangleOpenBondIndex a w h A) :=
    rectangleOpenBondIndexFintype a w h A
  let T := rectangleBondSignedTerm a w h F v.1
  let hindexEquiv : {b : RectanglePrimalBond a w h // q b} ≃
      rectangleOpenBondIndex a w h A := {
    toFun := fun b => ⟨b.1, by simpa [q, rectangleOpenBondIndex] using b.2⟩
    invFun := fun b => ⟨b.1, by simpa [q, rectangleOpenBondIndex] using b.2⟩
    left_inv := by intro b; apply Subtype.ext; rfl
    right_inv := by intro b; apply Subtype.ext; rfl }
  have hsub :
      (∑ b ∈ Finset.univ.filter q, T b) =
        ∑ b : rectangleOpenBondIndex a w h A, T b.1 := by
    calc
      _ = ∑ b : {b : RectanglePrimalBond a w h // q b}, T b.1 :=
        Finset.sum_subtype (p := q) (Finset.univ.filter q)
          (by intro b; simp [q]) T
      _ = ∑ b : {b : RectanglePrimalBond a w h // q b},
          T (hindexEquiv b).1 := by
        apply Finset.sum_congr rfl
        intro b hb
        change T b.1 = T b.1
        rfl
      _ = _ := Equiv.sum_comp hindexEquiv (fun b => T b.1)
  have hzero (b : RectanglePrimalBond a w h) (hb : ¬ q b) : T b = 0 := by
    have hb' : rectangleBondToGraphEdge a w h b ∉ A := by simpa [q] using hb
    have hz := rectangleOpenFlowZeroExtend_onClosed a w h A f b hb'
    simp [T, rectangleBondSignedTerm, F, hz]
  have hfull :
      (∑ b : RectanglePrimalBond a w h, T b) =
        ∑ b ∈ Finset.univ.filter q, T b := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hq : q b
    · simp [q, hq]
    · simp [q, hq, hzero b hq]
  have hedge (e : OpenEdgeIndex (rectangleGraph a w h) A) :
      T ((rectanglePrimalEdgeBondEquiv a w h) e.1) =
        (if (rectangleOpenEdgeOrientation a w h A).source e = v then f e else 0) -
          (if (rectangleOpenEdgeOrientation a w h A).target e = v then f e else 0) := by
    have hs : (rectangleOpenEdgeOrientation a w h A).source e = v ↔
        (rectanglePrimalEdgeBondEquiv a w h e.1).1.source = v.1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have ht : (rectangleOpenEdgeOrientation a w h A).target e = v ↔
        (rectanglePrimalEdgeBondEquiv a w h e.1).1.target = v.1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have hf : F ((rectanglePrimalEdgeBondEquiv a w h) e.1) = f e := by
      simp [F]
    simp [T, rectangleBondSignedTerm, hs, ht, hf]

  calc
    signedDivergence (rectangleGraph a w h) A
        (rectangleOpenEdgeOrientation a w h A) f v =
      ∑ e : OpenEdgeIndex (rectangleGraph a w h) A,
        ((if (rectangleOpenEdgeOrientation a w h A).source e = v then f e else 0) -
          (if (rectangleOpenEdgeOrientation a w h A).target e = v then f e else 0)) := by
      rw [signedDivergence_apply]
      rw [Finset.sum_sub_distrib]
    _ = ∑ e : OpenEdgeIndex (rectangleGraph a w h) A,
        T ((rectanglePrimalEdgeBondEquiv a w h) e.1) := by
      apply Finset.sum_congr rfl
      intro e he
      exact (hedge e).symm
    _ = ∑ b : rectangleOpenBondIndex a w h A, T b.1 := by
      exact Equiv.sum_comp (rectangleOpenBondEquiv a w h A)
        (fun b => T b.1)
    _ = ∑ b ∈ Finset.univ.filter q, T b := hsub.symm
    _ = ∑ b : RectanglePrimalBond a w h, T b := hfull.symm
    _ = rectanglePrimalFlowDivergence a w h F v.1 := by
      simpa [T] using (rectanglePrimalFlowDivergence_eq_allBonds a w h F v.1).symm



/-- The signed divergence kernel on actual open edges is the full normalized
bond divergence-free space intersected with the closed-bond zero subspace. -/
noncomputable def rectangleOpenFlowDivergenceKernelEquiv :
    LinearMap.ker (signedDivergence (rectangleGraph a w h) A
      (rectangleOpenEdgeOrientation a w h A)) ≃ₗ[ℝ]
      @Min.min (Submodule ℝ (RectanglePrimalFlow a w h)) inferInstance
        (rectangleOpenFlowSubmodule a w h A)
        (rectangleDivergenceFreeFlowSubmodule a w h) where
  toFun f := by
    refine ⟨(rectangleOpenFlowZeroExtendEquiv a w h A) f.1, ?_⟩
    change (↑((rectangleOpenFlowZeroExtendEquiv a w h A) f.1) ∈
      rectangleOpenFlowSubmodule a w h A) ∧
      ↑((rectangleOpenFlowZeroExtendEquiv a w h A) f.1) ∈
        rectangleDivergenceFreeFlowSubmodule a w h
    constructor
    · exact (rectangleOpenFlowZeroExtendEquiv a w h A f.1).2
    · intro z hz
      change rectanglePrimalFlowDivergence a w h
        (rectangleOpenFlowZeroExtend a w h A f.1) z = 0
      rw [← rectangleOpenFlowZeroExtend_signedDivergence a w h A f.1 ⟨z, hz⟩]
      exact congrFun f.2 ⟨z, hz⟩
  invFun F := by
    let g := (rectangleOpenFlowZeroExtendEquiv a w h A).symm
      ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩
    refine ⟨g, ?_⟩
    funext v
    have hF : rectangleOpenFlowZeroExtend a w h A g = F.1 := by
      exact congrArg Subtype.val
        (LinearEquiv.apply_symm_apply (rectangleOpenFlowZeroExtendEquiv a w h A)
          ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩)
    rw [rectangleOpenFlowZeroExtend_signedDivergence]
    rw [hF]
    exact (Submodule.mem_inf.mp F.2).2 v.1 v.2
  left_inv f := by
    apply Subtype.ext
    exact (rectangleOpenFlowZeroExtendEquiv a w h A).left_inv f.1
  right_inv F := by
    apply Subtype.ext
    change rectangleOpenFlowZeroExtend a w h A
      ((rectangleOpenFlowZeroExtendEquiv a w h A).symm
        ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩) = F.1
    exact congrArg Subtype.val
      ((rectangleOpenFlowZeroExtendEquiv a w h A).apply_symm_apply
        ⟨F.1, (Submodule.mem_inf.mp F.2).1⟩)
  map_add' f g := by
    apply Subtype.ext
    change rectangleOpenFlowZeroExtend a w h A (f.1 + g.1) =
      rectangleOpenFlowZeroExtend a w h A f.1 +
        rectangleOpenFlowZeroExtend a w h A g.1
    exact congrArg Subtype.val
      (map_add (rectangleOpenFlowZeroExtendEquiv a w h A) f.1 g.1)
  map_smul' c f := by
    apply Subtype.ext
    change rectangleOpenFlowZeroExtend a w h A (c • f.1) =
      c • rectangleOpenFlowZeroExtend a w h A f.1
    exact congrArg Subtype.val
      (map_smul (rectangleOpenFlowZeroExtendEquiv a w h A) c f.1)

end
end PottsDiscontinuity.FK
