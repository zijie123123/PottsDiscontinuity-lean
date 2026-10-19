module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.FreeAssociation

/-! Isometry and translation covariance of the actual free two-point function. -/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.Duality

open FK FK.Medial
noncomputable section

/-- A lattice isomorphism transports the actual open graph edge by edge. -/
def wholePlaneOpenGraphIso (e : squareLattice ≃g squareLattice) (ω : LatticeConfiguration) :
    wholePlaneOpenPrimalGraph ω ≃g
      wholePlaneOpenPrimalGraph (latticeConfigurationIsoHomeomorph e ω) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    have hidx (h : squareLattice.Adj (e.toEquiv u) (e.toEquiv v)) :
        SimpleGraph.Iso.mapEdgeSet e.symm ⟨s(e.toEquiv u, e.toEquiv v), squareLattice.mem_edgeSet.mpr h⟩ =
          ⟨s(u, v), squareLattice.mem_edgeSet.mpr (e.map_rel_iff'.1 h)⟩ := by
      apply Subtype.ext
      change Sym2.map e.symm s(e.toEquiv u, e.toEquiv v) = s(u, v)
      simp
    constructor
    · rintro ⟨hadj, hopen⟩
      refine ⟨e.map_rel_iff'.1 hadj, ?_⟩
      rw [latticeConfigurationIsoHomeomorph_apply, hidx hadj] at hopen
      exact hopen
    · rintro ⟨hadj, hopen⟩
      refine ⟨e.map_rel_iff'.2 hadj, ?_⟩
      rw [latticeConfigurationIsoHomeomorph_apply, hidx (e.map_rel_iff'.2 hadj)]
      exact hopen

lemma connectionEvent_preimage_iso (e : squareLattice ≃g squareLattice) (u v : LatticeVertex) :
    (latticeConfigurationIsoHomeomorph e) ⁻¹' connectionEvent (e u) (e v) =
      connectionEvent u v := by
  ext ω
  change (rcInfiniteOpenGraph (latticeConfigurationIsoHomeomorph e ω)).Reachable (e u) (e v) ↔
    (rcInfiniteOpenGraph ω).Reachable u v
  rw [← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph,
    ← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph]
  exact SimpleGraph.Iso.reachable_iff (φ := wholePlaneOpenGraphIso e ω)

/-- Actual free connectivity probabilities respect every box-preserving lattice symmetry. -/
theorem free_connection_symmetry (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (u v : LatticeVertex) :
    μ (connectionEvent (e u) (e v)) = μ (connectionEvent u v) := by
  have h := congrArg (fun ν : Measure LatticeConfiguration => ν (connectionEvent (e u) (e v)))
    (free_limit_map_latticeIso θ μ hμ e hbox)
  rw [Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable e)
    (connectionEvent_measurableSet _ _), connectionEvent_preimage_iso] at h
  exact h.symm

/-- The actual free two-point probability with one endpoint at the origin. -/
def twoPoint (μ : Measure LatticeConfiguration) (x : LatticeVertex) : ℝ :=
  μ.real (connectionEvent 0 x)

lemma connectionEvent_symm (u v : LatticeVertex) : connectionEvent u v = connectionEvent v u := by
  ext ω
  exact ⟨fun h => h.symm, fun h => h.symm⟩

lemma free_connection_translate (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (a u v : LatticeVertex) :
    μ (connectionEvent (u + a) (v + a)) = μ (connectionEvent u v) := by
  exact free_connection_symmetry θ μ hμ (latticeTranslationIso a)
      (fun c v r => mem_latticeBox_translate_iff a c v r) u v

/-- Infinite-volume FKG and translation invariance yield supermultiplicativity. -/
theorem twoPoint_mul_le (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (x y : LatticeVertex) :
    twoPoint μ x * twoPoint μ y ≤ twoPoint μ (x + y) := by
  have := hμ.1
  have h := free_connection_mul_le θ μ hμ 0 x (x + y)
  have ht := free_connection_translate θ μ hμ x 0 y
  simp only [zero_add, add_comm y x] at ht
  rw [ht] at h
  have hr := ENNReal.toReal_mono (measure_ne_top μ (connectionEvent 0 (x + y))) h
  simpa only [twoPoint, Measure.real_def, ENNReal.toReal_mul] using hr

lemma twoPoint_neg (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (x : LatticeVertex) :
    twoPoint μ (-x) = twoPoint μ x := by
  have ht := free_connection_translate θ μ hμ x 0 (-x)
  rw [zero_add, neg_add_cancel, connectionEvent_symm x 0] at ht
  exact congrArg ENNReal.toReal ht.symm

/-- Reflection in the horizontal axis. -/
def latticeFlipYIso : squareLattice ≃g squareLattice where
  toFun v := (v.1, -v.2)
  invFun v := (v.1, -v.2)
  left_inv v := by simp
  right_inv v := by simp
  map_rel_iff' := by
    intro u v
    change squareLattice.Adj (u.1, -u.2) (v.1, -v.2) ↔ squareLattice.Adj u v
    simp only [squareLattice_adj_iff]
    omega

lemma mem_latticeBox_flipY_iff (c v : LatticeVertex) (r : ℕ) :
    latticeFlipYIso v ∈ latticeBox (latticeFlipYIso c) r ↔ v ∈ latticeBox c r := by
  change (v.1, -v.2) ∈ latticeBox (c.1, -c.2) r ↔ v ∈ latticeBox c r
  simp only [mem_latticeBox]
  omega

lemma twoPoint_flipY (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (x : LatticeVertex) :
    twoPoint μ (x.1, -x.2) = twoPoint μ x := by
  have h := free_connection_symmetry θ μ hμ latticeFlipYIso mem_latticeBox_flipY_iff 0 x
  exact congrArg ENNReal.toReal h

lemma twoPoint_quarterTurn (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (x : LatticeVertex) :
    twoPoint μ (-x.2, x.1) = twoPoint μ x := by
  have h := free_connection_symmetry θ μ hμ latticeQuarterTurnIso
    (fun c v r => mem_latticeBox_quarterTurn_iff c v r) 0 x
  exact congrArg ENNReal.toReal h

end
end PottsDiscontinuity.Duality
