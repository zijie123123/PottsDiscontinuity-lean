module

public import PottsDiscontinuity.FK.Graph
public import PottsDiscontinuity.TorusCrossing.Lattice

/-!
# Graphs given by their edge-end maps

Both the primal board graph and the dual board graph are of the form: vertex set `P`
(a finite set of cells) and one edge `ends m` for each medial vertex `m` of a finite set `M`.
This file builds the corresponding simple graph, the bijection between `M` and its edge set,
the translation between `FK.Configuration` and finite sets of medial vertices, and relates
actual connectivity to a cell-level reflexive-transitive closure.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity

section EndGraph

variable (ends : Cell → Cell × Cell) (P M : Finset Cell)

/-- The graph on `P` with an edge `ends m` for each `m ∈ M`. -/
def endGraph : SimpleGraph P :=
  SimpleGraph.fromRel (fun c d => ∃ m ∈ M, ends m = (c.1, d.1))

variable {ends P M}

theorem endGraph_adj (c d : P) :
    (endGraph ends P M).Adj c d ↔
      c ≠ d ∧ ((∃ m ∈ M, ends m = (c.1, d.1)) ∨ (∃ m ∈ M, ends m = (d.1, c.1))) := by
  unfold endGraph; rw [SimpleGraph.fromRel_adj]

/-- Structural hypotheses making `m ↦ ends m` an honest edge indexing. -/
structure EndData (ends : Cell → Cell × Cell) (P M : Finset Cell) : Prop where
  mem : ∀ m ∈ M, (ends m).1 ∈ P ∧ (ends m).2 ∈ P
  ne : ∀ m, (ends m).1 ≠ (ends m).2
  inj : ∀ m m', ends m = ends m' ∨ ends m = (ends m').swap → m = m'

variable (hD : EndData ends P M)
include hD

/-- The edge of `endGraph` carried by a medial vertex. -/
def endEdge (m : M) : (endGraph ends P M).edgeSet :=
  ⟨s((⟨(ends m.1).1, (hD.mem m.1 m.2).1⟩ : P), (⟨(ends m.1).2, (hD.mem m.1 m.2).2⟩ : P)), by
    rw [SimpleGraph.mem_edgeSet, endGraph_adj]
    refine ⟨fun h => hD.ne m.1 (congrArg Subtype.val h), Or.inl ⟨m.1, m.2, rfl⟩⟩⟩

theorem endEdge_injective : Function.Injective (endEdge hD) := by
  intro m m' h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  simp only [endEdge, Sym2.eq_iff] at h'
  apply hD.inj
  rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2)
  · right; exact Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2)

theorem endEdge_surjective : Function.Surjective (endEdge hD) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ c d =>
    rw [SimpleGraph.mem_edgeSet, endGraph_adj] at he
    rcases he.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
      simp only [endEdge, Sym2.eq_iff]
      left
      exact ⟨Subtype.ext (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩
    · refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
      simp only [endEdge, Sym2.eq_iff]
      right
      exact ⟨Subtype.ext (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩

/-- Medial vertices are in bijection with the edges of the graph. -/
noncomputable def endEdgeEquiv : M ≃ (endGraph ends P M).edgeSet :=
  Equiv.ofBijective (endEdge hD) ⟨endEdge_injective hD, endEdge_surjective hD⟩

/-- A finite set of medial vertices, read as an FK configuration (elements outside `M`
are ignored). -/
noncomputable def cfgOf (A : Finset Cell) : FK.Configuration (endGraph ends P M) :=
  (A.subtype (· ∈ M)).map (endEdgeEquiv hD).toEmbedding

/-- The medial vertices carrying the open edges of an FK configuration. -/
noncomputable def openMedials (C : FK.Configuration (endGraph ends P M)) : Finset Cell :=
  (C.map (endEdgeEquiv hD).symm.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_openMedials (C : FK.Configuration (endGraph ends P M)) (m : Cell) :
    m ∈ openMedials hD C ↔ ∃ hm : m ∈ M, endEdgeEquiv hD ⟨m, hm⟩ ∈ C := by
  unfold openMedials
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨((endEdgeEquiv hD).symm e).2, by simpa using he⟩
  · rintro ⟨hm, h⟩
    exact ⟨_, ⟨_, h, rfl⟩, by simp⟩

theorem openMedials_subset (C : FK.Configuration (endGraph ends P M)) :
    openMedials hD C ⊆ M := fun m hm => ((mem_openMedials hD C m).1 hm).1

theorem mem_cfgOf (A : Finset Cell) (m : M) :
    endEdgeEquiv hD m ∈ cfgOf hD A ↔ m.1 ∈ A := by
  unfold cfgOf
  simp

theorem openMedials_cfgOf (A : Finset Cell) (hA : A ⊆ M) : openMedials hD (cfgOf hD A) = A := by
  ext m
  rw [mem_openMedials]
  constructor
  · rintro ⟨hm, h⟩
    exact (mem_cfgOf hD A ⟨m, hm⟩).1 h
  · intro h
    exact ⟨hA h, (mem_cfgOf hD A ⟨m, hA h⟩).2 h⟩

theorem cfgOf_openMedials (C : FK.Configuration (endGraph ends P M)) :
    cfgOf hD (openMedials hD C) = C := by
  ext e
  obtain ⟨m, rfl⟩ := (endEdgeEquiv hD).surjective e
  rw [mem_cfgOf, mem_openMedials]
  constructor
  · rintro ⟨hm, h⟩; exact h
  · intro h; exact ⟨m.2, h⟩

theorem card_cfgOf (A : Finset Cell) (hA : A ⊆ M) : (cfgOf hD A).card = A.card := by
  have := congrArg Finset.card (openMedials_cfgOf hD A hA)
  rw [← this]
  unfold openMedials; simp

/-- One step of open connectivity at the level of cells. -/
def StepRel (ends : Cell → Cell × Cell) (A : Finset Cell) (x y : Cell) : Prop :=
  ∃ m ∈ A, ends m = (x, y) ∨ ends m = (y, x)

theorem endEdgeEquiv_val (m : M) :
    ((endEdgeEquiv hD m : (endGraph ends P M).edgeSet) : Sym2 P) =
      s((⟨(ends m.1).1, (hD.mem m.1 m.2).1⟩ : P), (⟨(ends m.1).2, (hD.mem m.1 m.2).2⟩ : P)) := rfl

theorem openGraph_adj_iff (C : FK.Configuration (endGraph ends P M)) (c d : P) :
    (FK.openGraph (endGraph ends P M) C).Adj c d ↔ StepRel ends (openMedials hD C) c.1 d.1 := by
  rw [FK.openGraph_adj, FK.openEdges]
  constructor
  · rintro ⟨e, he, heq⟩
    obtain ⟨m, rfl⟩ := (endEdgeEquiv hD).surjective e
    refine ⟨m.1, (mem_openMedials hD C _).2 ⟨m.2, he⟩, ?_⟩
    rw [endEdgeEquiv_val, Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2)
    · right; exact Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2)
  · rintro ⟨m, hm, h⟩
    obtain ⟨hmM, hmC⟩ := (mem_openMedials hD C m).1 hm
    refine ⟨endEdgeEquiv hD ⟨m, hmM⟩, hmC, ?_⟩
    rw [endEdgeEquiv_val, Sym2.eq_iff]
    rcases h with h | h
    · left
      exact ⟨Subtype.ext (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩
    · right
      exact ⟨Subtype.ext (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩

omit hD in
theorem stepRel_symm {A : Finset Cell} {x y : Cell} (h : StepRel ends A x y) : StepRel ends A y x := by
  obtain ⟨m, hm, h⟩ := h
  exact ⟨m, hm, h.symm⟩

/-- Actual open connectivity equals reflexive-transitive closure of cell-level steps. -/
theorem actualConnected_iff (C : FK.Configuration (endGraph ends P M)) (c d : P) :
    FK.ActualConnected (endGraph ends P M) C c d ↔
      Relation.ReflTransGen (StepRel ends (openMedials hD C)) c.1 d.1 := by
  unfold FK.ActualConnected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    exact (Relation.ReflTransGen.lift Subtype.val (fun a b hab => (openGraph_adj_iff hD C a b).1 hab)) _ _ h
  · intro h
    have key : ∀ y : Cell, Relation.ReflTransGen (StepRel ends (openMedials hD C)) c.1 y →
        ∃ y' : P, y'.1 = y ∧ Relation.ReflTransGen (FK.openGraph (endGraph ends P M) C).Adj c y' := by
      intro y hy
      induction hy with
      | refl => exact ⟨c, rfl, Relation.ReflTransGen.refl⟩
      | @tail b z _ hstep ih =>
        obtain ⟨y', rfl, hy'⟩ := ih
        obtain ⟨m, hm, hmz⟩ := hstep
        have hmM := openMedials_subset hD C hm
        have hz : z ∈ P := by
          rcases hmz with hmz | hmz
          · have := (hD.mem m hmM).2; rwa [hmz] at this
          · have := (hD.mem m hmM).1; rwa [hmz] at this
        refine ⟨⟨z, hz⟩, rfl, hy'.tail ?_⟩
        rw [openGraph_adj_iff hD]
        exact ⟨m, hm, hmz⟩
    obtain ⟨y', hy', hr⟩ := key d.1 h
    have : y' = d := Subtype.ext hy'
    rwa [this] at hr

/-- The end of `m` different from `z` (when `z` is an end of `m`). -/
def otherEnd (ends : Cell → Cell × Cell) (z m : Cell) : Cell :=
  if (ends m).1 = z then (ends m).2 else (ends m).1

omit hD in
theorem ends_eq_of_mem {m z : Cell} (hne : (ends m).1 ≠ (ends m).2) (hz : z = (ends m).1 ∨ z = (ends m).2) :
    ends m = (z, otherEnd ends z m) ∨ ends m = (otherEnd ends z m, z) := by
  unfold otherEnd
  rcases hz with hz | hz
  · left
    have h1 : (ends m).1 = z := hz.symm
    simp only [h1, ite_true]
    exact Prod.ext hz.symm rfl
  · right
    have : ¬ (ends m).1 = z := fun e => hne (e.trans hz)
    simp only [this, ite_false]
    exact Prod.ext rfl hz.symm

omit hD in
theorem otherEnd_ne {m z : Cell} (hne : (ends m).1 ≠ (ends m).2) (hz : z = (ends m).1 ∨ z = (ends m).2) :
    otherEnd ends z m ≠ z := by
  intro e
  rcases ends_eq_of_mem hne hz with h | h
  · apply hne
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [h1, h2, e]
  · apply hne
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [h1, h2, e]

/-- The degree of a vertex is the number of medial vertices having it as an end. -/
theorem degree_eq [DecidableEq Cell] (z : P) [DecidableRel (endGraph ends P M).Adj] :
    (endGraph ends P M).degree z =
      (M.filter (fun m => z.1 = (ends m).1 ∨ z.1 = (ends m).2)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  symm
  have hmem : ∀ m ∈ M, (z.1 = (ends m).1 ∨ z.1 = (ends m).2) → otherEnd ends z.1 m ∈ P := by
    intro m hm hz
    have h1 := hD.mem m hm
    unfold otherEnd
    split_ifs
    · exact h1.2
    · exact h1.1
  refine Finset.card_bij
    (fun m hm => (⟨otherEnd ends z.1 m, hmem m (Finset.mem_filter.1 hm).1
      (Finset.mem_filter.1 hm).2⟩ : P)) ?_ ?_ ?_
  · intro m hm
    obtain ⟨hmM, hz⟩ := Finset.mem_filter.1 hm
    rw [SimpleGraph.mem_neighborFinset, endGraph_adj]
    have hne := hD.ne m
    refine ⟨fun h => otherEnd_ne hne hz (congrArg Subtype.val h).symm, ?_⟩
    rcases ends_eq_of_mem hne hz with h | h
    · exact Or.inl ⟨m, hmM, h⟩
    · exact Or.inr ⟨m, hmM, h⟩
  · intro m hm m' hm' h
    obtain ⟨hmM, hz⟩ := Finset.mem_filter.1 hm
    obtain ⟨hmM', hz'⟩ := Finset.mem_filter.1 hm'
    have h' : otherEnd ends z.1 m = otherEnd ends z.1 m' := congrArg Subtype.val h
    apply hD.inj
    rcases ends_eq_of_mem (hD.ne m) hz with e | e <;>
      rcases ends_eq_of_mem (hD.ne m') hz' with e' | e'
    · left; rw [e, e', h']
    · right; rw [e, e', h']; rfl
    · right; rw [e, e', h']; rfl
    · left; rw [e, e', h']
  · intro d hd
    rw [SimpleGraph.mem_neighborFinset, endGraph_adj] at hd
    obtain ⟨hzd, hd⟩ := hd
    rcases hd with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · have hz : z.1 = (ends m).1 := (congrArg Prod.fst h).symm
      refine ⟨m, Finset.mem_filter.2 ⟨hm, Or.inl hz⟩, Subtype.ext ?_⟩
      show otherEnd ends z.1 m = d.1
      unfold otherEnd; simp only [← hz, ite_true]; exact congrArg Prod.snd h
    · have hz : z.1 = (ends m).2 := (congrArg Prod.snd h).symm
      refine ⟨m, Finset.mem_filter.2 ⟨hm, Or.inr hz⟩, Subtype.ext ?_⟩
      show otherEnd ends z.1 m = d.1
      have hne : ¬ (ends m).1 = z.1 := by
        intro e
        apply hzd
        apply Subtype.ext
        have := congrArg Prod.fst h
        simp only at this
        rw [← this]; exact e.symm
      unfold otherEnd; simp only [hne, ite_false]; exact congrArg Prod.fst h

end EndGraph

end PottsDiscontinuity.TorusCrossing
