/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenForest
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenSymmDiff

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

/-- The symmetric difference of the faces in a finite list, with repetitions
interpreted by parity. -/
def faceSymmDiffList {V I : Type*} (F : I → SimpleGraph V) : List I → SimpleGraph V
  | [] => ⊥
  | i :: is => F i ∆ faceSymmDiffList F is

@[instance_reducible]
noncomputable def locallyFiniteOfFintype {V : Type*} [Fintype V] (G : SimpleGraph V) :
    LocallyFinite G := fun v =>
  Fintype.ofInjective (fun x : G.neighborSet v => x.1) Subtype.val_injective

/-- If even-degree faces have distinct triangular pivot edges, they span every
 even-degree subgraph if deleting all pivots leaves an acyclic graph. -/
theorem exists_faceSymmDiffList_of_even_subgraph
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (F : I → SimpleGraph V) (p : I → Sym2 V) (rank : I → ℕ)
    [LocallyFinite G] [∀ i, LocallyFinite (F i)]
    (hFle : ∀ i, F i ≤ G)
    (hFeven : ∀ i v, Even ((F i).degree v))
    (hpF : ∀ i, p i ∈ (F i).edgeSet)
    (htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i)
    (hacyclic : (G.deleteEdges (Set.range p)).IsAcyclic)
    (H : SimpleGraph V) [LocallyFinite H]
    (hle : H ≤ G) (hHeven : ∀ v, Even (H.degree v)) :
    ∃ L : List I, L.Nodup ∧ faceSymmDiffList F L = H := by
  classical
  let aux : ∀ (S : Finset I) (K : SimpleGraph V) [LocallyFinite K],
      K ≤ G → (∀ v, Even (K.degree v)) →
      (∀ j, j ∉ S → p j ∉ K.edgeSet) →
      (∀ i ∈ S, ∀ j, j ∉ S → rank i ≤ rank j) →
      ∃ L : List I, L.Nodup ∧ (∀ i ∈ L, i ∈ S) ∧ faceSymmDiffList F L = K := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih K instK hKG hKeven hKnopivot hrank
    by_cases hSn : S.Nonempty
    · obtain ⟨f, hfS, hfmax⟩ := S.exists_max_image rank hSn
      let S' := S.erase f
      have hfS' : f ∉ S' := Finset.notMem_erase _ _
      have hS'sub : S' ⊂ S := Finset.erase_ssubset hfS
      have hrank' : ∀ i ∈ S', ∀ j, j ∉ S' → rank i ≤ rank j := by
        intro i hi j hj
        have hiS : i ∈ S := Finset.mem_of_mem_erase hi
        by_cases hfj : j = f
        · subst j
          exact hfmax i hiS
        · have hjS : j ∉ S := by
            intro h
            exact hj (Finset.mem_erase.mpr ⟨hfj, h⟩)
          exact hrank i hiS j hjS
      by_cases hfp : p f ∈ K.edgeSet
      · let K' := K ∆ F f
        have hK'le : K' ≤ G := by
          intro v w hvw
          simp only [K', symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj] at hvw ⊢
          rcases hvw with h | h
          · exact hKG h.1
          · exact hFle f h.1
        let : LocallyFinite K' := locallyFiniteOfFintype K'
        have hK'even : ∀ v, Even (K'.degree v) := by
          intro v
          exact degree_even_symmDiff K (F f) hKeven (hFeven f) v
        have hK'no : ∀ j, j ∉ S' → p j ∉ K'.edgeSet := by
          intro j hj hjK'
          have hK'edge := hjK'
          rw [show K' = K ∆ F f by rfl, symmDiff_def, SimpleGraph.edgeSet_sup,
            SimpleGraph.edgeSet_sdiff] at hK'edge
          simp only [SimpleGraph.edgeSet_sdiff, Set.mem_union, Set.mem_sdiff] at hK'edge
          rcases hK'edge with h | h
          · by_cases hfj : j = f
            · subst j
              exact h.2 (hpF f)
            · have hjS : j ∉ S := by
                intro hjS
                exact hj (Finset.mem_erase.mpr ⟨hfj, hjS⟩)
              exact hKnopivot j hjS h.1
          · by_cases hfj : j = f
            · subst j
              exact h.2 hfp
            · have hjS : j ∉ S := by
                intro hjS
                exact hj (Finset.mem_erase.mpr ⟨hfj, hjS⟩)
              rcases htri f j h.1 with hEq | hlt
              · exact hfj hEq
              · have hleRank := hrank f hfS j hjS
                omega
        obtain ⟨L, hLnodup, hLmem, hLdecomp⟩ :=
          ih S' hS'sub K' hK'le hK'even hK'no hrank'
        refine ⟨f :: L, ?_, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨by
            intro hfL
            exact hfS' (hLmem f hfL), hLnodup⟩
        · intro i hi
          simp only [List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact hfS
          · exact Finset.mem_of_mem_erase (hLmem i hi)
        · change F f ∆ faceSymmDiffList F L = K
          rw [hLdecomp]
          change F f ∆ (K ∆ F f) = K
          rw [← symmDiff_assoc, symmDiff_symmDiff_self']
      · have hK'no : ∀ j, j ∉ S' → p j ∉ K.edgeSet := by
          intro j hj
          by_cases hfj : j = f
          · subst j
            simpa [S'] using hfp
          · have hjS : j ∉ S := by
              intro hjS
              exact hj (Finset.mem_erase.mpr ⟨hfj, hjS⟩)
            exact hKnopivot j hjS
        obtain ⟨L, hLnodup, hLmem, hLdecomp⟩ :=
          ih S' hS'sub K hKG hKeven hK'no hrank'
        refine ⟨L, hLnodup, ?_, hLdecomp⟩
        intro i hi
        exact Finset.mem_of_mem_erase (hLmem i hi)
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSn
      subst S
      have hKleDel : K ≤ G.deleteEdges (Set.range p) := by
        intro v w hvw
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hKG hvw, ?_⟩
        intro hp
        obtain ⟨j, hpeq⟩ := Set.mem_range.mp hp
        apply hKnopivot j (by simp)
        simpa only [hpeq, SimpleGraph.mem_edgeSet] using hvw
      have hKacyclic : K.IsAcyclic := hacyclic.anti hKleDel
      have hKevenN : ∀ v, Even ((K.neighborSet v).ncard) := by
        intro v
        simpa only [SimpleGraph.ncard_neighborSet] using hKeven v
      have hKbot : K = ⊥ := eq_bot_of_isAcyclic_even_degree K hKacyclic (by
        intro v
        rw [← SimpleGraph.ncard_neighborSet]
        exact hKevenN v)
      subst K
      exact ⟨[], List.nodup_nil, by simp, by simp [faceSymmDiffList]⟩
  have hinitrank : ∀ i ∈ Finset.univ, ∀ j, j ∉ Finset.univ → rank i ≤ rank j := by
    simp
  obtain ⟨L, hLnodup, hLmem, hLdecomp⟩ :=
    aux Finset.univ H hle hHeven (by simp) hinitrank
  exact ⟨L, hLnodup, hLdecomp⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
