/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.FK.BoxTranslation

@[expose] public section

namespace PottsDiscontinuity.FK
open MeasureTheory
noncomputable section

/-- The literal counterclockwise quarter-turn `(x,y) ↦ (-y,x)`. -/
def latticeQuarterTurn (v : LatticeVertex) : LatticeVertex := (-v.2, v.1)

/-- The inverse quarter-turn `(x,y) ↦ (y,-x)`. -/
def latticeQuarterTurnInv (v : LatticeVertex) : LatticeVertex := (v.2, -v.1)

/-- The literal reflection `(x,y) ↦ (-x,y)`. -/
def latticeReflection (v : LatticeVertex) : LatticeVertex := (-v.1, v.2)

@[simp] theorem latticeQuarterTurnInv_quarterTurn (v : LatticeVertex) :
    latticeQuarterTurnInv (latticeQuarterTurn v) = v := by
  ext <;> simp [latticeQuarterTurn, latticeQuarterTurnInv]

@[simp] theorem latticeQuarterTurn_quarterTurnInv (v : LatticeVertex) :
    latticeQuarterTurn (latticeQuarterTurnInv v) = v := by
  ext <;> simp [latticeQuarterTurn, latticeQuarterTurnInv]

@[simp] theorem latticeReflection_involutive (v : LatticeVertex) :
    latticeReflection (latticeReflection v) = v := by
  ext <;> simp [latticeReflection]

lemma squareLattice_adj_quarterTurn_iff (u v : LatticeVertex) :
    squareLattice.Adj (latticeQuarterTurn u) (latticeQuarterTurn v) ↔
      squareLattice.Adj u v := by
  simp only [squareLattice_adj_iff, latticeQuarterTurn]
  omega

/-- The actual graph isomorphism for the literal quarter-turn. -/
def latticeQuarterTurnIso : squareLattice ≃g squareLattice where
  toFun := latticeQuarterTurn
  invFun := latticeQuarterTurnInv
  left_inv := latticeQuarterTurnInv_quarterTurn
  right_inv := latticeQuarterTurn_quarterTurnInv
  map_rel_iff' := by
    intro u v
    exact squareLattice_adj_quarterTurn_iff u v

lemma mem_latticeBox_quarterTurn_iff (c v : LatticeVertex) (r : ℕ) :
    latticeQuarterTurn v ∈ latticeBox (latticeQuarterTurn c) r ↔
      v ∈ latticeBox c r := by
  rw [mem_latticeBox, mem_latticeBox]
  simp only [latticeQuarterTurn]
  omega

/-- A graph isomorphism preserving the lattice boxes induces the corresponding
finite induced-graph isomorphism. -/
def boxGraphIsoOfLatticeIso
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) : boxGraph c r ≃g boxGraph (e c) r where
  toEquiv :=
    { toFun := fun v => ⟨e v.1, (hbox c v.1 r).2 v.2⟩
      invFun := fun v => ⟨e.symm v.1, by
        have hv : e (e.symm v.1) ∈ latticeBox (e c) r := by simp
        exact (hbox c (e.symm v.1) r).mp hv⟩
      left_inv := by intro v; apply Subtype.ext; exact e.left_inv v.1
      right_inv := by intro v; apply Subtype.ext; exact e.right_inv v.1 }
  map_rel_iff' := by
    intro u v
    change squareLattice.Adj (e u.1) (e v.1) ↔ squareLattice.Adj u.1 v.1
    exact e.map_rel_iff'

/-- Push configurations on the whole lattice along the original-edge map of a
lattice graph isomorphism. -/
def latticeConfigurationIsoHomeomorph (e : squareLattice ≃g squareLattice) :
    LatticeConfiguration ≃ₜ LatticeConfiguration :=
  Homeomorph.piCongrLeft (Y := fun _ : squareLattice.edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet e)

@[simp] theorem latticeConfigurationIsoHomeomorph_apply
    (e : squareLattice ≃g squareLattice) (ω : LatticeConfiguration)
    (b : squareLattice.edgeSet) :
    latticeConfigurationIsoHomeomorph e ω b =
      ω (SimpleGraph.Iso.mapEdgeSet e.symm b) := by
  simp [latticeConfigurationIsoHomeomorph, Homeomorph.piCongrLeft,
    Equiv.piCongrLeft, SimpleGraph.Iso.mapEdgeSet,
    SimpleGraph.Hom.mapEdgeSet]

theorem latticeConfigurationIsoHomeomorph_measurable
    (e : squareLattice ≃g squareLattice) :
    Measurable (latticeConfigurationIsoHomeomorph e) :=
  (latticeConfigurationIsoHomeomorph e).continuous_toFun.measurable

lemma boxEdgeEmbedding_iso_commute
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) (b : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding (e c) r
        (SimpleGraph.Iso.mapEdgeSet (boxGraphIsoOfLatticeIso e hbox c r) b) =
      SimpleGraph.Iso.mapEdgeSet e (boxEdgeEmbedding c r b) := by
  apply Subtype.ext
  simp only [boxEdgeEmbedding, boxGraphEmbedding,
    SimpleGraph.Embedding.mapEdgeSet_apply, SimpleGraph.Iso.mapEdgeSet_apply,
    SimpleGraph.Hom.mapEdgeSet_coe, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding]
  rw [Sym2.map_map, Sym2.map_map]
  congr 1

lemma boxEmbeddedEdgeSet_iso_commute
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) (A : Configuration (boxGraph c r)) :
    (configurationIso (boxGraphIsoOfLatticeIso e hbox c r) A).map
      (boxEdgeEmbedding (e c) r) =
      (A.map (boxEdgeEmbedding c r)).map
        (SimpleGraph.Iso.mapEdgeSet e).toEmbedding := by
  change (A.map (configurationIsoEdgeEquiv (boxGraphIsoOfLatticeIso e hbox c r)).toEmbedding).map
      (boxEdgeEmbedding (e c) r) =
    (A.map (boxEdgeEmbedding c r)).map
      (SimpleGraph.Iso.mapEdgeSet e).toEmbedding
  rw [Finset.map_map, Finset.map_map]
  have hEmb :
      (configurationIsoEdgeEquiv (boxGraphIsoOfLatticeIso e hbox c r)).toEmbedding.trans
          (boxEdgeEmbedding (e c) r) =
        (boxEdgeEmbedding c r).trans
          (SimpleGraph.Iso.mapEdgeSet e).toEmbedding := by
    apply Function.Embedding.ext
    intro b
    exact boxEdgeEmbedding_iso_commute e hbox c r b
  rw [hEmb]

theorem boxConfiguration_iso_commute
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) (A : Configuration (boxGraph c r)) :
    boxConfiguration (e c) r (configurationIso (boxGraphIsoOfLatticeIso e hbox c r) A) =
      latticeConfigurationIsoHomeomorph e (boxConfiguration c r A) := by
  funext b
  simp only [boxConfiguration, latticeConfigurationIsoHomeomorph_apply]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [boxEmbeddedEdgeSet_iso_commute]
  rw [Finset.mem_map_equiv]
  simp [SimpleGraph.Iso.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet]

theorem boxLaw_iso_map
    (q : Parameters) (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) :
    PMF.map (latticeConfigurationIsoHomeomorph e).toEquiv (boxLaw q c r) =
      boxLaw q (e c) r := by
  rw [boxLaw, boxLaw, PMF.map_comp]
  have hcomp :
      (latticeConfigurationIsoHomeomorph e).toEquiv ∘ boxConfiguration c r =
        boxConfiguration (e c) r ∘ configurationIso (boxGraphIsoOfLatticeIso e hbox c r) := by
    funext A
    exact (boxConfiguration_iso_commute e hbox c r A).symm
  rw [hcomp, ← PMF.map_comp]
  rw [law_configurationIso_map q (boxGraphIsoOfLatticeIso e hbox c r)
      (BoundaryCondition.free ∅)]
  rw [boundaryConditionIso_free_empty]

theorem boxProbabilityMeasure_iso_map
    (q : Parameters) (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure.map (boxProbabilityMeasure q c r)
      (latticeConfigurationIsoHomeomorph e) =
        boxProbabilityMeasure q (e c) r := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (latticeConfigurationIsoHomeomorph e) (boxLaw q c r).toMeasure =
    (boxLaw q (e c) r).toMeasure
  rw [PMF.toMeasure_map _ _ (latticeConfigurationIsoHomeomorph_measurable e)]
  exact congrArg PMF.toMeasure (boxLaw_iso_map q e hbox c r)

end
end PottsDiscontinuity.FK

