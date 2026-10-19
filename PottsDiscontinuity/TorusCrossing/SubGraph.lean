module

public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.TorusCrossing.Markov
public import PottsDiscontinuity.TorusCrossing.TwoBoard

/-!
# The graph of unexplored edges

For a set `Ex` of medial vertices of a board `Q` (the explored edges), the unexplored edges
`Un = Q.inner \ Ex` form a graph `subG` on the cells they touch; it embeds in `Q.pG`.  We express
the Markov property for the freezing of `Ex` in terms of cell-level events.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (Q : Rect) (Ex : Finset Cell)

/-- The unexplored medial vertices. -/
def unx : Finset Cell := Q.inner \ Ex

/-- Cells touched by an unexplored edge. -/
noncomputable def vrx : Finset Cell :=
  (Q.unx Ex).image (fun m => (primalEnds m).1) ∪ (Q.unx Ex).image (fun m => (primalEnds m).2)

variable {Q Ex}

theorem mem_unx {m : Cell} : m ∈ Q.unx Ex ↔ m ∈ Q.inner ∧ m ∉ Ex := by
  unfold unx; exact Finset.mem_sdiff

theorem mem_vrx {c : Cell} : c ∈ Q.vrx Ex ↔ Vtx (Q.unx Ex) c := by
  unfold vrx Vtx
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact ⟨m, hm, Or.inl rfl⟩
    · exact ⟨m, hm, Or.inr rfl⟩
  · rintro ⟨m, hm, rfl | rfl⟩
    · exact Or.inl ⟨m, hm, rfl⟩
    · exact Or.inr ⟨m, hm, rfl⟩

variable (Q Ex)

theorem unx_subset_inner : Q.unx Ex ⊆ Q.inner := Finset.sdiff_subset

theorem subData : EndData primalEnds (Q.vrx Ex) (Q.unx Ex) where
  mem m hm := ⟨mem_vrx.2 ⟨m, hm, Or.inl rfl⟩, mem_vrx.2 ⟨m, hm, Or.inr rfl⟩⟩
  ne := primalEnds_ne
  inj _ _ h := primalEnds_inj h

theorem vrx_subset_pcells : Q.vrx Ex ⊆ Q.pcells := fun _c hc =>
  Vtx_mem_pcells (unx_subset_inner Q Ex) (mem_vrx.1 hc)

/-- The graph of unexplored edges. -/
noncomputable abbrev subG : SimpleGraph (Q.vrx Ex) := endGraph primalEnds (Q.vrx Ex) (Q.unx Ex)

/-- The embedding of the vertices of the unexplored graph into those of the board graph. -/
noncomputable def subEmb : (Q.vrx Ex) ↪ Q.pcells where
  toFun v := ⟨v.1, vrx_subset_pcells Q Ex v.2⟩
  inj' := by
    intro a b h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)

theorem subLe : (Q.subG Ex).map (subEmb Q Ex) ≤ Q.pG := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
  rw [endGraph_adj] at hab ⊢
  refine ⟨fun h => hab.1 ((subEmb Q Ex).injective h), ?_⟩
  rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
  · exact Or.inl ⟨m, unx_subset_inner Q Ex hm, h⟩
  · exact Or.inr ⟨m, unx_subset_inner Q Ex hm, h⟩

/-- The edges of the board graph that are not edges of the unexplored graph. -/
noncomputable def remG : FK.Configuration Q.pG :=
  FK.subgraphRemovedEdges ((Q.subG Ex).map (Q.subEmb Ex)) Q.pG

theorem endEdge_mem_remG {m : Cell} (hm : m ∈ Q.inner) :
    endEdgeEquiv Q.pData ⟨m, hm⟩ ∈ Q.remG Ex ↔ m ∉ Q.unx Ex := by
  unfold remG
  rw [FK.mem_subgraphRemovedEdges, endEdgeEquiv_val, SimpleGraph.mem_edgeSet, SimpleGraph.map_adj]
  constructor
  · intro h hmU
    apply h
    refine ⟨⟨(primalEnds m).1, mem_vrx.2 ⟨m, hmU, Or.inl rfl⟩⟩,
      ⟨(primalEnds m).2, mem_vrx.2 ⟨m, hmU, Or.inr rfl⟩⟩, ?_, rfl, rfl⟩
    rw [endGraph_adj]
    exact ⟨fun h => primalEnds_ne m (congrArg Subtype.val h), Or.inl ⟨m, hmU, rfl⟩⟩
  · intro h hadj
    obtain ⟨a, b, hab, ha, hb⟩ := hadj
    apply h
    rw [endGraph_adj] at hab
    have ha' : a.1 = (primalEnds m).1 := congrArg Subtype.val ha
    have hb' : b.1 = (primalEnds m).2 := congrArg Subtype.val hb
    rcases hab.2 with ⟨m', hm', he⟩ | ⟨m', hm', he⟩
    · have : m' = m := primalEnds_inj (Or.inl (by rw [he, ha', hb']))
      rw [← this]; exact hm'
    · have : m' = m := primalEnds_inj (Or.inr (by rw [he, ha', hb']; rfl))
      rw [← this]; exact hm'

theorem embeddedEdge_endEdge {m : Cell} (hm : m ∈ Q.unx Ex) :
    FK.embeddedEdgeEmbedding (Q.subG Ex) Q.pG (Q.subEmb Ex) (Q.subLe Ex)
      (endEdgeEquiv (Q.subData Ex) ⟨m, hm⟩) =
        endEdgeEquiv Q.pData ⟨m, unx_subset_inner Q Ex hm⟩ := by
  apply Subtype.ext
  rw [FK.embeddedEdgeEmbedding_coe, endEdgeEquiv_val, endEdgeEquiv_val]
  rfl

theorem openMedials_restr (C : FK.Configuration Q.pG) :
    openMedials (Q.subData Ex)
      (FK.embeddedConfigurationRestriction (Q.subG Ex) Q.pG (Q.subEmb Ex) (Q.subLe Ex) C) =
        openMedials Q.pData C ∩ Q.unx Ex := by
  ext m
  rw [Finset.mem_inter, mem_openMedials, mem_openMedials]
  constructor
  · rintro ⟨hm, h⟩
    rw [FK.mem_embeddedConfigurationRestriction] at h
    refine ⟨⟨unx_subset_inner Q Ex hm, ?_⟩, hm⟩
    rwa [embeddedEdge_endEdge] at h
  · rintro ⟨⟨hm, h⟩, hmU⟩
    refine ⟨hmU, ?_⟩
    rw [FK.mem_embeddedConfigurationRestriction, embeddedEdge_endEdge]
    exact h

variable {Q Ex}

theorem cfgOf_subset_remG {H₀ : Finset Cell} (hH : H₀ ⊆ Ex) :
    cfgOf Q.pData H₀ ⊆ Q.remG Ex := by
  intro e he
  obtain ⟨m, rfl⟩ := (endEdgeEquiv Q.pData).surjective e
  rw [mem_cfgOf] at he
  exact (endEdge_mem_remG Q Ex m.2).2 (fun hU => (mem_unx.1 hU).2 (hH he))

/-- The frozen configuration of the explored edges. -/
noncomputable def froz {H₀ : Finset Cell} (hH : H₀ ⊆ Ex) :
    FK.RemovedConfiguration Q.pG (Q.remG Ex) :=
  ⟨cfgOf Q.pData H₀, cfgOf_subset_remG hH⟩

theorem mem_inter_remG (C : FK.Configuration Q.pG) {m : Cell}
    (hm : m ∈ Q.inner) :
    (endEdgeEquiv Q.pData ⟨m, hm⟩ ∈ C ∧ endEdgeEquiv Q.pData ⟨m, hm⟩ ∈ Q.remG Ex) ↔
      (m ∈ openMedials Q.pData C ∧ m ∈ Ex) := by
  rw [endEdge_mem_remG Q Ex hm, mem_openMedials]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hm, h1⟩, ?_⟩
    by_contra hnE
    exact h2 (mem_unx.2 ⟨hm, hnE⟩)
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, fun hU => (mem_unx.1 hU).2 h2⟩

theorem frozen_iff (hEx : Ex ⊆ Q.inner) {H₀ : Finset Cell} (hH : H₀ ⊆ Ex)
    (C : FK.Configuration Q.pG) :
    C ∈ FK.frozenStateEvent (Q.remG Ex) (froz hH) ↔ openMedials Q.pData C ∩ Ex = H₀ := by
  unfold FK.frozenStateEvent
  rw [Set.mem_ofPred_eq, Finset.ext_iff]
  simp only [Finset.mem_inter]
  constructor
  · intro h
    ext m
    rw [Finset.mem_inter]
    constructor
    · intro hm
      have hmI := hEx hm.2
      have h1 := (mem_inter_remG C hmI).2 hm
      exact (mem_cfgOf Q.pData H₀ ⟨m, hmI⟩).1 ((h _).1 h1)
    · intro hm
      have hmI := hEx (hH hm)
      have h1 : endEdgeEquiv Q.pData ⟨m, hmI⟩ ∈ cfgOf Q.pData H₀ :=
        (mem_cfgOf Q.pData H₀ ⟨m, hmI⟩).2 hm
      exact (mem_inter_remG C hmI).1 ((h _).2 h1)
  · intro h e
    obtain ⟨m, rfl⟩ := (endEdgeEquiv Q.pData).surjective e
    rw [mem_inter_remG C m.2]
    change _ ↔ endEdgeEquiv Q.pData m ∈ cfgOf Q.pData H₀
    rw [mem_cfgOf, ← h, Finset.mem_inter]

/-- A boundary condition given by a setoid on all vertices. -/
def bcOfSetoid {V : Type*} (s : Setoid V) : FK.BoundaryCondition V where
  boundary := Set.univ
  partition := s
  supported := fun _ => Or.inr ⟨Set.mem_univ _, Set.mem_univ _⟩

variable (Q Ex)

/-- Probability of a cell-level event of the unexplored edges, under the FK model of the unexplored
graph with boundary condition given by the pullback of a setoid on the board vertices. -/
noncomputable def nuMeasure (θ : FK.Parameters) (P : Setoid Q.pcells) (𝒮 : Set (Finset Cell)) :
    ENNReal :=
  FK.measure (Q.subG Ex) θ (bcOfSetoid (Setoid.comap (Q.subEmb Ex) P))
    {C' | openMedials (Q.subData Ex) C' ∈ 𝒮}

variable {Q Ex}

attribute [local instance] FK.configurationMeasurableSpace in
/-- **Domain Markov at the cell level.** -/
theorem markov_cell (θ : FK.Parameters) (ξ : FK.BoundaryCondition Q.pcells) (hEx : Ex ⊆ Q.inner)
    {H₀ : Finset Cell} (hH : H₀ ⊆ Ex) (𝒮 : Set (Finset Cell)) :
    FK.measure Q.pG θ ξ {C | openMedials Q.pData C ∩ Ex = H₀ ∧
        openMedials Q.pData C ∩ Q.unx Ex ∈ 𝒮} =
      nuMeasure Q Ex θ (FK.componentSetoid Q.pG ξ (cfgOf Q.pData H₀)) 𝒮 *
        FK.measure Q.pG θ ξ {C | openMedials Q.pData C ∩ Ex = H₀} := by
  have h := embedded_frozen_measure_eq (Q.subG Ex) Q.pG (Q.subEmb Ex) (Q.subLe Ex) θ ξ (froz hH)
    {C' | openMedials (Q.subData Ex) C' ∈ 𝒮}
  have hset1 : {C | FK.embeddedConfigurationRestriction (Q.subG Ex) Q.pG (Q.subEmb Ex)
        (Q.subLe Ex) C ∈ {C' | openMedials (Q.subData Ex) C' ∈ 𝒮}} ∩
      FK.frozenStateEvent (FK.subgraphRemovedEdges ((Q.subG Ex).map (Q.subEmb Ex)) Q.pG) (froz hH) =
        {C | openMedials Q.pData C ∩ Ex = H₀ ∧ openMedials Q.pData C ∩ Q.unx Ex ∈ 𝒮} := by
    ext C
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [openMedials_restr]
    have := frozen_iff hEx hH C
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨this.1 h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, this.2 h1⟩
  have hset2 : FK.frozenStateEvent (FK.subgraphRemovedEdges ((Q.subG Ex).map (Q.subEmb Ex)) Q.pG)
      (froz hH) = {C | openMedials Q.pData C ∩ Ex = H₀} := by
    ext C
    exact frozen_iff hEx hH C
  rw [hset1, hset2] at h
  rw [h]
  unfold nuMeasure
  congr 1

theorem openMedials_mono' {C C' : FK.Configuration Q.pG} (h : C ⊆ C') :
    openMedials Q.pData C ⊆ openMedials Q.pData C' := by
  intro m hm
  obtain ⟨hmI, he⟩ := (mem_openMedials Q.pData C m).1 hm
  exact (mem_openMedials Q.pData C' m).2 ⟨hmI, h he⟩

theorem openMedials_mono_sub {C C' : FK.Configuration (Q.subG Ex)} (h : C ⊆ C') :
    openMedials (Q.subData Ex) C ⊆ openMedials (Q.subData Ex) C' := by
  intro m hm
  obtain ⟨hmI, he⟩ := (mem_openMedials (Q.subData Ex) C m).1 hm
  exact (mem_openMedials (Q.subData Ex) C' m).2 ⟨hmI, h he⟩

attribute [local instance] FK.configurationMeasurableSpace in
theorem nu_mono (θ : FK.Parameters) {P P' : Setoid Q.pcells}
    (hPP : ∀ x y : Q.pcells, Vtx (Q.unx Ex) x.1 → Vtx (Q.unx Ex) y.1 → P.r x y → P'.r x y)
    {𝒮 : Set (Finset Cell)} (h𝒮 : ∀ A B : Finset Cell, A ⊆ B → A ∈ 𝒮 → B ∈ 𝒮) :
    (nuMeasure Q Ex θ P 𝒮).toReal ≤ (nuMeasure Q Ex θ P' 𝒮).toReal := by
  unfold nuMeasure
  apply FK.measure_boundary_comparison
  · intro a b hab
    exact hPP (Q.subEmb Ex a) (Q.subEmb Ex b) (mem_vrx.1 a.2) (mem_vrx.1 b.2) hab
  · intro C C' hCC' hC
    exact h𝒮 _ _ (openMedials_mono_sub hCC') hC

end Rect

end PottsDiscontinuity.TorusCrossing
