module

public import PottsDiscontinuity.FK.BoxLimits
public import PottsDiscontinuity.Potts.NestedBoxComparison

/-! Whole-lattice extensions and cylinders for the literal ghost law. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

/-- Open exterior extension, retaining all sampled internal bonds. -/
def openExtension (V : Finset (ℤ × ℤ))
    (C : FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) : FK.LatticeConfiguration :=
  fun e => decide (∀ f, FK.frozenEdgeEmbedding V f = e → f ∈ C)

@[simp] theorem openExtension_at (V : Finset (ℤ × ℤ))
    (C : FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (f : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet) :
    openExtension V C (FK.frozenEdgeEmbedding V f) = decide (f ∈ C) := by
  have h : (∀ g, FK.frozenEdgeEmbedding V g = FK.frozenEdgeEmbedding V f → g ∈ C) ↔ f ∈ C := by
    constructor
    · exact fun h => h f rfl
    · intro hf g hg
      exact (FK.frozenEdgeEmbedding V).injective hg ▸ hf
  simp only [openExtension, h]

/-- The literal ghost measure on a common edge-configuration space. -/
def ghostBoxConfiguration (n : ℕ) (ω : LiteralBond (box n) → Bool) : FK.LatticeConfiguration :=
  openExtension (box n) (FK.boolConfigurationEquiv _ (fun e => ω (.inl e)))

def ghostBoxProbabilityMeasure (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    ProbabilityMeasure FK.LatticeConfiguration :=
  ⟨((ghostRCLaw q hq (box n) β hβ).map (ghostBoxConfiguration n)).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- The same extension applied to the ordinary wired box law. -/
def openBoxProbabilityMeasure (θ : FK.Parameters) (n : ℕ) : ProbabilityMeasure FK.LatticeConfiguration :=
  FK.frozenExtendedProbabilityMeasure θ (box n) 1 (openExtension (box n))

theorem openBoxProbabilityMeasure_eq_wired (θ : FK.Parameters) (n : ℕ) :
    openBoxProbabilityMeasure θ n = FK.wiredBoxProbabilityMeasure θ (0, 0) n := by
  unfold openBoxProbabilityMeasure
  have key : ∀ (c : FK.LatticeVertex) (r : ℕ) (S : Finset (ℤ × ℤ)), FK.latticeBox c r = S →
      FK.frozenExtendedProbabilityMeasure θ S 1 (openExtension S) =
        FK.wiredBoxProbabilityMeasure θ c r := by
    rintro c r S rfl
    have hext : openExtension (FK.latticeBox c r) = FK.wiredBoxConfiguration c r := by
      funext C e
      unfold openExtension FK.wiredBoxConfiguration
      exact decide_eq_decide.mpr Iff.rfl
    rw [hext]
    exact FK.frozenExtendedProbabilityMeasure_wired θ c r
  exact key (0, 0) n _ (FK.latticeBox_origin_eq_box n)

def openBoxCylinderEvent (n : ℕ) (F : Finset squareLattice.edgeSet) :
    Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  {C | ∀ e ∈ F, ∀ f, FK.frozenEdgeEmbedding (box n) f = e → f ∈ C}

theorem openBoxCylinderEvent_upper (n : ℕ) (F : Finset squareLattice.edgeSet) :
    IsUpperSet (openBoxCylinderEvent n F) := by
  intro C D hCD hC e he f hf
  exact hCD (hC e he f hf)

theorem openExtension_mem_allOpen (n : ℕ)
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))
    (F : Finset squareLattice.edgeSet) :
    openExtension (box n) C ∈ FK.LatticeConfiguration.allOpen F ↔ C ∈ openBoxCylinderEvent n F := by
  simp only [openExtension, FK.LatticeConfiguration.allOpen, openBoxCylinderEvent,
    Set.mem_ofPred_eq, decide_eq_true_eq]

theorem openBoxProbabilityMeasure_allOpen (θ : FK.Parameters) (n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    (openBoxProbabilityMeasure θ n).toMeasure (FK.LatticeConfiguration.allOpen F) =
      FK.measure _ θ (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box n)})
        (openBoxCylinderEvent n F) := by
  change (((FK.law _ θ (FK.frozenBoundaryCondition (box n) 1)).map
    (openExtension (box n))).toMeasure _) = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (FK.LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 1
  ext C
  exact openExtension_mem_allOpen n C F

theorem nestedEdgeEmbedding_compatible {m n : ℕ} (h : m ≤ n)
    (e : (squareLattice.induce (box m : Set (ℤ × ℤ))).edgeSet) :
    FK.frozenEdgeEmbedding (box n)
      (FK.embeddedEdgeEmbedding _ _ (nestedBoxEmbedding h) (nestedBox_map_le h) e) =
      FK.frozenEdgeEmbedding (box m) e := by
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map (nestedBoxEmbedding h) e.val) =
    Sym2.map Subtype.val e.val
  rw [Sym2.map_map]
  rfl

/-- Once the support lies in the smaller box, the local event is unchanged by restriction. -/
theorem nestedBoxEvent_openBoxCylinderEvent {m n : ℕ} (h : m ≤ n)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, ∃ f, FK.frozenEdgeEmbedding (box m) f = e) :
    nestedBoxEvent h (openBoxCylinderEvent m F) = openBoxCylinderEvent n F := by
  ext C
  constructor
  · intro hC e he f hf
    obtain ⟨g, hg⟩ := hF e he
    have hread := hC e he g hg
    rw [FK.mem_embeddedConfigurationRestriction] at hread
    have hfg : FK.embeddedEdgeEmbedding _ _ (nestedBoxEmbedding h) (nestedBox_map_le h) g = f :=
      (FK.frozenEdgeEmbedding (box n)).injective ((nestedEdgeEmbedding_compatible h g).trans
        (hg.trans hf.symm))
    exact hfg ▸ hread
  · intro hC e he f hf
    rw [FK.mem_embeddedConfigurationRestriction]
    exact hC e he _ ((nestedEdgeEmbedding_compatible h f).trans hf)

end
end PottsDiscontinuity.Potts
