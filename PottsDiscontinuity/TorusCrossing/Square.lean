module

public import PottsDiscontinuity.FK.BoundaryPartitionLaw
public import PottsDiscontinuity.FK.Isomorphism
public import PottsDiscontinuity.TorusCrossing.Hex
public import PottsDiscontinuity.TorusCrossing.Rotation
public import PottsDiscontinuity.TorusCrossing.WiringCompare

/-!
# The mixed-boundary square crossing bound ([BefDum12])

For an odd square board with the bottom and top rows wired (separately) and free sides, the
critical random-cluster measure gives probability at least `1/(1+q)` (hence at least `1/(1+q^2)`)
to an open path joining the two wired rows.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

/-- Vertical (bottom-to-top) crossing event of the primal board. -/
def crossP : Set (FK.Configuration R.pG) :=
  {C | ∃ u v : R.pcells, u.1.2 = R.y0 ∧ v.1.2 = R.y0 + R.h ∧ FK.ActualConnected R.pG C u v}

/-- Horizontal (left-to-right) crossing event of the dual board. -/
def crossD : Set (FK.Configuration R.dG) :=
  {D | ∃ z z' : R.dcells, z.1.1 = R.x0 ∧ z'.1.1 = R.x0 + R.w ∧ FK.ActualConnected R.dG D z z'}

/-- The bottom and top rows wired into a single class. -/
def togBC : FK.BoundaryCondition R.pcells :=
  FK.BoundaryCondition.wired {c | c.1.2 = R.y0 ∨ c.1.2 = R.y0 + R.h}

theorem isUpperSet_crossP : IsUpperSet R.crossP := by
  intro A B hAB hA
  obtain ⟨u, v, hu, hv, h⟩ := hA
  exact ⟨u, v, hu, hv, FK.actualConnected_mono hAB h⟩

theorem wcell_mem_pcells (hw : 0 < R.w) (j : ℤ) (hj1 : R.y0 ≤ j) (hj2 : j ≤ R.y0 + R.h) :
    R.wcell j ∈ R.pcells := by
  have hw' : (0 : ℤ) < R.w := by exact_mod_cast hw
  rw [mem_pcells, mem_cells]
  have := R.wcell_primal j
  have h2 := R.wcell_row j
  have h3 := R.wcell_col j
  refine ⟨⟨?_, ?_, ?_, ?_⟩, this⟩ <;> omega

theorem togBC_wireStep (hw : 0 < R.w) :
    IsWireStep R.sepBC R.togBC
      ⟨R.wcell R.y0, R.wcell_mem_pcells hw R.y0 le_rfl (by omega)⟩
      ⟨R.wcell (R.y0 + R.h), R.wcell_mem_pcells hw _ (by omega) le_rfl⟩ := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    rcases hab with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl h.1, Or.inl h.2⟩
    · exact Or.inr ⟨Or.inr h.1, Or.inr h.2⟩
  · intro x y hxy
    rcases hxy with h | ⟨hx, hy⟩
    · exact Or.inl (Or.inl h)
    · refine Or.inr ⟨?_, ?_⟩ <;> [skip; skip]
      · rcases hx with hx | hx
        · left; exact Or.inr (Or.inl ⟨hx, R.wcell_row _⟩)
        · right; exact Or.inr (Or.inr ⟨hx, R.wcell_row _⟩)
      · rcases hy with hy | hy
        · left; exact Or.inr (Or.inl ⟨hy, R.wcell_row _⟩)
        · right; exact Or.inr (Or.inr ⟨hy, R.wcell_row _⟩)


theorem rotIso_symm_val (hsq : R.w = R.h) (hodd : R.w % 2 = 1) (a : R.pcells) :
    (((R.rotIso hsq hodd).symm a : R.dcells) : Cell) = R.rotInv a.1 := rfl

theorem rotIso_val (hsq : R.w = R.h) (hodd : R.w % 2 = 1) (z : R.dcells) :
    (((R.rotIso hsq hodd) z : R.pcells) : Cell) = R.rot z.1 := rfl

theorem boundaryIso_partition (hsq : R.w = R.h) (hodd : R.w % 2 = 1) :
    (FK.boundaryConditionIso (R.rotIso hsq hodd) R.dualBC).partition = R.togBC.partition := by
  apply Setoid.ext
  intro a b
  have hw : (R.w : ℤ) = R.h := by exact_mod_cast hsq
  have key : ∀ c : R.pcells,
      ((R.rotIso hsq hodd).symm c).1.1 = R.x0 ∨ ((R.rotIso hsq hodd).symm c).1.1 = R.x0 + R.w ↔
        (c.1.2 = R.y0 ∨ c.1.2 = R.y0 + R.h) := by
    intro c
    rw [rotIso_symm_val]
    unfold rotInv
    dsimp only
    omega
  change ((R.rotIso hsq hodd).symm a = (R.rotIso hsq hodd).symm b ∨
      ((R.rotIso hsq hodd).symm a ∈ {z : R.dcells | z.1.1 = R.x0 ∨ z.1.1 = R.x0 + R.w} ∧
      (R.rotIso hsq hodd).symm b ∈ {z : R.dcells | z.1.1 = R.x0 ∨ z.1.1 = R.x0 + R.w})) ↔ _
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl ((R.rotIso hsq hodd).symm.injective h)
    · exact Or.inr ⟨(key a).1 h1, (key b).1 h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (congrArg _ h)
    · exact Or.inr ⟨(key a).2 h1, (key b).2 h2⟩

theorem crossD_eq_preimage (hsq : R.w = R.h) (hodd : R.w % 2 = 1) :
    R.crossD = (FK.configurationIso (R.rotIso hsq hodd)) ⁻¹' R.crossP := by
  have hw : (R.w : ℤ) = R.h := by exact_mod_cast hsq
  ext D
  simp only [Set.mem_preimage, crossD, crossP, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, z', hz, hz', h⟩
    refine ⟨(R.rotIso hsq hodd) z', (R.rotIso hsq hodd) z, ?_, ?_, ?_⟩
    · rw [rotIso_val]; unfold rot; dsimp only; omega
    · rw [rotIso_val]; unfold rot; dsimp only; omega
    · rw [FK.actualConnected_configurationIso]
      exact h.symm
  · rintro ⟨u, v, hu, hv, h⟩
    refine ⟨(R.rotIso hsq hodd).symm v, (R.rotIso hsq hodd).symm u, ?_, ?_, ?_⟩
    · rw [rotIso_symm_val]; unfold rotInv; dsimp only; omega
    · rw [rotIso_symm_val]; unfold rotInv; dsimp only; omega
    · have := (FK.actualConnected_configurationIso (R.rotIso hsq hodd) D
        ((R.rotIso hsq hodd).symm v) ((R.rotIso hsq hodd).symm u)).1
      rw [RelIso.apply_symm_apply, RelIso.apply_symm_apply] at this
      exact this h.symm

attribute [local instance] FK.configurationMeasurableSpace

noncomputable local instance pEdgeFintype' : Fintype R.pG.edgeSet := Fintype.ofFinite _
noncomputable local instance dEdgeFintype' : Fintype R.dG.edgeSet := Fintype.ofFinite _

theorem measure_dual_crossD (hsq : R.w = R.h) (hodd : R.w % 2 = 1) (q : Set.Ici (1 : ℝ)) :
    FK.measure R.dG (critParams q) R.dualBC R.crossD =
      FK.measure R.pG (critParams q) R.togBC R.crossP := by
  have hlaw := FK.law_configurationIso_map (critParams q) (R.rotIso hsq hodd) R.dualBC
  rw [FK.law_eq_of_boundary_partition_eq (critParams q) _ R.togBC (R.boundaryIso_partition hsq hodd)]
    at hlaw
  have hmap := congrArg PMF.toMeasure hlaw
  rw [← PMF.toMeasure_map _ _ measurable_from_top] at hmap
  rw [R.crossD_eq_preimage hsq hodd]
  change (FK.law R.dG (critParams q) R.dualBC).toMeasure _ = _
  rw [← MeasureTheory.Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
  exact congrArg (fun μ : MeasureTheory.Measure (FK.Configuration R.pG) => μ R.crossP) hmap


theorem crossP_connected_wcells (hw : 0 < R.w) :
    ∀ C ∈ R.crossP, (FK.componentSetoid R.pG R.sepBC C).r
      ⟨R.wcell R.y0, R.wcell_mem_pcells hw R.y0 le_rfl (by omega)⟩
      ⟨R.wcell (R.y0 + R.h), R.wcell_mem_pcells hw _ (by omega) le_rfl⟩ := by
  intro C ⟨u, v, hu, hv, h⟩
  have s := FK.componentSetoid R.pG R.sepBC C
  have h1 : (FK.componentSetoid R.pG R.sepBC C).r u v :=
    FK.actualConnected_component R.pG R.sepBC C h
  have h2 : (FK.componentSetoid R.pG R.sepBC C).r
      ⟨R.wcell R.y0, R.wcell_mem_pcells hw R.y0 le_rfl (by omega)⟩ u :=
    FK.boundary_component R.pG R.sepBC C (Or.inr (Or.inl ⟨R.wcell_row _, hu⟩))
  have h3 : (FK.componentSetoid R.pG R.sepBC C).r v
      ⟨R.wcell (R.y0 + R.h), R.wcell_mem_pcells hw _ (by omega) le_rfl⟩ :=
    FK.boundary_component R.pG R.sepBC C (Or.inr (Or.inr ⟨hv, R.wcell_row _⟩))
  exact (FK.componentSetoid R.pG R.sepBC C).trans h2
    ((FK.componentSetoid R.pG R.sepBC C).trans h1 h3)

theorem compl_crossP_subset (hh : 0 < R.h) (hw : 0 < R.w) :
    R.crossPᶜ ⊆ R.dualEquiv ⁻¹' R.crossD := by
  intro C hC
  exact R.hex hh hw C hC

/-- **Mixed-boundary square crossing** ([BefDum12]): for an odd square board at the self-dual
point, wired on the bottom and top rows (separately) and free on the sides, the probability of an
open path between the two wired rows is at least `1 / (1 + q)`. -/
theorem crossing_ge (q : Set.Ici (1 : ℝ)) (hs : R.w = R.h) (hodd : R.w % 2 = 1) (hw : 0 < R.w) :
    1 / (1 + q.val) ≤ (FK.measure R.pG (critParams q) R.sepBC R.crossP).toReal := by
  have hh : 0 < R.h := hs ▸ hw
  have hq : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  set x := (FK.measure R.pG (critParams q) R.sepBC R.crossP).toReal with hx
  have h1 : (FK.measure R.pG (critParams q) R.sepBC R.crossPᶜ).toReal = 1 - x := by
    have := FK.measure_isProbabilityMeasure R.pG (critParams q) R.sepBC
    have := MeasureTheory.measureReal_compl (μ := FK.measure R.pG (critParams q) R.sepBC)
      (s := R.crossP) (MeasurableSpace.measurableSet_top)
    simpa [MeasureTheory.Measure.real] using this
  have h2 : (FK.measure R.pG (critParams q) R.sepBC R.crossPᶜ).toReal ≤
      (FK.measure R.pG (critParams q) R.sepBC (R.dualEquiv ⁻¹' R.crossD)).toReal :=
    ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
      (MeasureTheory.measure_mono (R.compl_crossP_subset hh hw))
  rw [R.measure_preimage_dualEquiv hh q, R.measure_dual_crossD hs hodd q] at h2
  have h3 := measure_wire_le (critParams q) (R.togBC_wireStep hw) R.crossP
    (R.crossP_connected_wcells hw)
  rw [critParams_val] at h3
  rw [h1] at h2
  have h4 : 1 - x ≤ q.val * x := h2.trans h3
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Rect

end PottsDiscontinuity.TorusCrossing
