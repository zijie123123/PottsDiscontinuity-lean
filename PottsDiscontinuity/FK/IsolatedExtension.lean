/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import PottsDiscontinuity.FK.PositiveAssociation
public import PottsDiscontinuity.FK.ProbabilityProduct

/-!
# Extending a finite free FK graph by isolated vertices

An injective vertex map transports every original edge and adds no edges at the
other vertices. Those vertices are retained as separate components. Their fixed
factor in the FK weight cancels exactly from the normalized probability law.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V W : Type*} (G : SimpleGraph V) (f : V ↪ W)

/-- The mapped graph's actual paths either have equal endpoints or come from original paths. -/
theorem reachable_isolatedExtension (x y : W) :
    (G.map f).Reachable x y ↔
      x = y ∨ ∃ u v, G.Reachable u v ∧ f u = x ∧ f v = y := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inl rfl
    | @tail y z h hyz ih =>
      obtain ⟨u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj f G y z).mp hyz
      rcases ih with rfl | ⟨a, b, hab, ha, hb⟩
      · exact Or.inr ⟨u, v, huv.reachable, hu, hv⟩
      · have hbu : b = u := f.injective (hb.trans hu.symm)
        subst u
        exact Or.inr ⟨a, v, hab.trans huv.reachable, ha, hv⟩
  · rintro (rfl | ⟨u, v, huv, rfl, rfl⟩)
    · exact .refl _
    · exact huv.map (SimpleGraph.Embedding.map f G).toHom

/-- No new connection is created between original vertices. -/
theorem reachable_isolatedExtension_apply (u v : V) :
    (G.map f).Reachable (f u) (f v) ↔ G.Reachable u v := by
  rw [reachable_isolatedExtension]
  constructor
  · rintro (h | ⟨a, b, hab, ha, hb⟩)
    · exact f.injective h ▸ SimpleGraph.Reachable.refl _
    · simpa only [f.injective ha, f.injective hb] using hab
  · intro h
    exact Or.inr ⟨u, v, h, rfl, rfl⟩

/-- Each added vertex really is isolated, including for actual path connectivity. -/
theorem reachable_isolatedExtension_outside {x y : W} (hx : x ∉ Set.range f) :
    (G.map f).Reachable x y ↔ x = y := by
  rw [reachable_isolatedExtension]
  exact ⟨fun h => h.elim id (fun ⟨u, _, _, hu, _⟩ => (hx ⟨u, hu⟩).elim), Or.inl⟩

/-- Original connected components and the added singleton vertices enumerate all
components of the extended graph, without dropping isolated original vertices. -/
def isolatedExtensionComponentEquiv :
    G.ConnectedComponent ⊕ {w : W // w ∉ Set.range f} ≃ (G.map f).ConnectedComponent :=
  Equiv.ofBijective
    (Sum.elim (SimpleGraph.ConnectedComponent.map (SimpleGraph.Embedding.map f G).toHom)
      (fun w => (G.map f).connectedComponentMk w.val)) (by
    constructor
    · rintro (a | a) (b | b) h
      · apply congrArg Sum.inl
        induction a using SimpleGraph.ConnectedComponent.ind with
        | h u =>
          induction b using SimpleGraph.ConnectedComponent.ind with
          | h v =>
            exact SimpleGraph.ConnectedComponent.sound
              ((reachable_isolatedExtension_apply G f u v).mp
                (SimpleGraph.ConnectedComponent.exact h))
      · induction a using SimpleGraph.ConnectedComponent.ind with
        | h u =>
          have hconn := (SimpleGraph.ConnectedComponent.exact h).symm
          have heq := (reachable_isolatedExtension_outside G f b.property).mp hconn
          exact (b.property ⟨u, heq.symm⟩).elim
      · induction b using SimpleGraph.ConnectedComponent.ind with
        | h v =>
          have hconn := SimpleGraph.ConnectedComponent.exact h
          have heq := (reachable_isolatedExtension_outside G f a.property).mp hconn
          exact (a.property ⟨v, heq.symm⟩).elim
      · apply congrArg Sum.inr
        apply Subtype.ext
        exact (reachable_isolatedExtension_outside G f a.property).mp
          (SimpleGraph.ConnectedComponent.exact h)
    · intro c
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h w =>
        by_cases hw : w ∈ Set.range f
        · obtain ⟨v, rfl⟩ := hw
          exact ⟨Sum.inl (G.connectedComponentMk v), rfl⟩
        · exact ⟨Sum.inr ⟨w, hw⟩, rfl⟩)

/-- Every edge of the mapped graph is the image of a unique original edge. -/
def isolatedExtensionEdgeEquiv : G.edgeSet ≃ (G.map f).edgeSet :=
  Equiv.ofBijective (SimpleGraph.Embedding.map f G).mapEdgeSet (by
    constructor
    · exact (SimpleGraph.Embedding.map f G).mapEdgeSet.injective
    · rintro ⟨e, he⟩
      rw [SimpleGraph.edgeSet_map] at he
      obtain ⟨a, ha, rfl⟩ := he
      exact ⟨⟨a, ha⟩, rfl⟩)

@[simp] theorem isolatedExtensionEdgeEquiv_coe (e : G.edgeSet) :
    (isolatedExtensionEdgeEquiv G f e).val = f.sym2Map e.val := rfl

/-- Transport precisely the sampled original edges, not the added vertices. -/
def isolatedExtensionConfigurationEquiv : Configuration G ≃ Configuration (G.map f) :=
  (isolatedExtensionEdgeEquiv G f).finsetCongr

@[simp] theorem isolatedExtensionConfigurationEquiv_val (A : Configuration G) :
    isolatedExtensionConfigurationEquiv G f A = A.map (isolatedExtensionEdgeEquiv G f).toEmbedding :=
  rfl

/-- Edge inclusion is unchanged under the actual transport. -/
def isolatedExtensionConfigurationOrderIso : Configuration G ≃o Configuration (G.map f) where
  toEquiv := isolatedExtensionConfigurationEquiv G f
  map_rel_iff' := Finset.map_subset_map

@[simp] theorem card_isolatedExtensionConfigurationEquiv (A : Configuration G) :
    (isolatedExtensionConfigurationEquiv G f A).card = A.card := Finset.card_map _

/-- The open graph is exactly the injective image of the original open graph. -/
theorem openGraph_isolatedExtension (A : Configuration G) :
    openGraph (G.map f) (isolatedExtensionConfigurationEquiv G f A) =
      (openGraph G A).map f := by
  apply SimpleGraph.edgeSet_injective
  rw [openGraph_edgeSet, SimpleGraph.edgeSet_map, openGraph_edgeSet]
  simp only [openEdges, isolatedExtensionConfigurationEquiv_val, Finset.coe_map,
    Set.image_image]
  rfl

/-- The count includes exactly one additional component for every new vertex. -/
theorem componentCount_isolatedExtension [Finite V] [Finite W]
    (B : Set V) (C : Set W) (A : Configuration G) :
    componentCount (G.map f) (BoundaryCondition.free C)
        (isolatedExtensionConfigurationEquiv G f A) =
      componentCount G (BoundaryCondition.free B) A + Nat.card {w : W // w ∉ Set.range f} := by
  simp only [componentCount, componentSetoid_free, openGraph_isolatedExtension]
  change Nat.card ((openGraph G A).map f).ConnectedComponent =
    Nat.card (openGraph G A).ConnectedComponent + _
  rw [← Nat.card_congr (isolatedExtensionComponentEquiv (openGraph G A) f), Nat.card_sum]

/-- Actual original-vertex connectivity is unchanged in the transported configuration. -/
theorem actualConnected_isolatedExtension (A : Configuration G) (u v : V) :
    ActualConnected (G.map f) (isolatedExtensionConfigurationEquiv G f A) (f u) (f v) ↔
      ActualConnected G A u v := by
  rw [ActualConnected, ActualConnected, openGraph_isolatedExtension,
    reachable_isolatedExtension_apply]

section Finite

variable [Finite V] [Finite W]
local instance isolatedExtensionOriginalEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance isolatedExtensionMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _

omit [Finite V] [Finite W] in
/-- Vertex extension adds no sampled edges. -/
theorem isolatedExtension_edge_card : Nat.card (G.map f).edgeSet = Nat.card G.edgeSet :=
  (Nat.card_congr (isolatedExtensionEdgeEquiv G f)).symm

/-- Added isolated vertices contribute a fixed positive factor to every weight.
The labels of the free boundary sets can be arbitrary on either vertex carrier. -/
theorem weight_isolatedExtension (q : Parameters) (B : Set V) (C : Set W)
    (A : Configuration G) :
    weight (G.map f) q (BoundaryCondition.free C) (isolatedExtensionConfigurationEquiv G f A) =
      weight G q (BoundaryCondition.free B) A * q.val ^ Nat.card {w : W // w ∉ Set.range f} := by
  rw [weight, weight, card_isolatedExtensionConfigurationEquiv, isolatedExtension_edge_card,
    componentCount_isolatedExtension G f B C A, pow_add]
  simp only [mul_assoc]

/-- The very same factor appears in the complete finite partition function. -/
theorem partitionFunction_isolatedExtension (q : Parameters) (B : Set V) (C : Set W) :
    partitionFunction (G.map f) q (BoundaryCondition.free C) =
      partitionFunction G q (BoundaryCondition.free B) * q.val ^ Nat.card {w : W // w ∉ Set.range f} := by
  unfold partitionFunction FiniteProbability.partition
  rw [← (isolatedExtensionConfigurationEquiv G f).sum_comp]
  simp_rw [weight_isolatedExtension G f q B C]
  rw [Finset.sum_mul]

/-- The isolated-vertex factor cancels, yielding exact normalized probabilities. -/
theorem configurationProbability_isolatedExtension (q : Parameters)
    (B : Set V) (C : Set W) (A : Configuration G) :
    configurationProbability (G.map f) q (BoundaryCondition.free C)
        (isolatedExtensionConfigurationEquiv G f A) =
      configurationProbability G q (BoundaryCondition.free B) A := by
  rw [configurationProbability, configurationProbability,
    weight_isolatedExtension G f q B C A, partitionFunction_isolatedExtension G f q B C]
  exact mul_div_mul_right _ _ (pow_ne_zero _ (ne_of_gt (clusterWeight_pos q)))

/-- The entire free FK probability law is unchanged by adding isolated vertices,
under the proved bijection of actual original-edge configurations. -/
theorem law_isolatedExtension_map (q : Parameters) (B : Set V) (C : Set W) :
    (law G q (BoundaryCondition.free B)).map (isolatedExtensionConfigurationEquiv G f) =
      law (G.map f) q (BoundaryCondition.free C) := by
  ext A
  obtain ⟨A, rfl⟩ := (isolatedExtensionConfigurationEquiv G f).surjective A
  rw [FiniteProbability.map_equiv_apply, Equiv.symm_apply_apply, law_apply, law_apply,
    configurationProbability_isolatedExtension G f q B C A]

end Finite
end
end PottsDiscontinuity.FK
