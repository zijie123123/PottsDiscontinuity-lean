module

public import PottsDiscontinuity.TorusCrossing.Planar

/-!
# The dual board graph is connected
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

theorem step_of_inner {m : Cell} (hm : m ∈ R.inner) :
    StepRel dualEnds R.inner (dualEnds m).1 (dualEnds m).2 := ⟨m, hm, Or.inl rfl⟩

/-- Every odd cell is joined to a bottom-row odd cell. -/
theorem dual_to_bottom (hw : 0 < R.w) :
    ∀ n : ℕ, ∀ z : Cell, z ∈ R.dcells → z.2 - R.y0 = n →
      ∃ b ∈ R.dcells, b.2 = R.y0 ∧ Relation.ReflTransGen (StepRel dualEnds R.inner) z b := by
  intro n
  induction n with
  | zero =>
    intro z hz hn
    exact ⟨z, hz, by have := mem_cells.1 (mem_dcells.1 hz).1; omega, Relation.ReflTransGen.refl⟩
  | succ n ih =>
    intro z hz hn
    have hzc := mem_cells.1 (mem_dcells.1 hz).1
    have hzp := (mem_dcells.1 hz).2
    have hw' : (0 : ℤ) < R.w := by exact_mod_cast hw
    by_cases hx : R.x0 < z.1
    · -- step to (z.1 - 1, z.2 - 1) through the medial vertex z
      have hm : z ∈ R.inner := by
        rw [mem_inner]; push_cast at hn; omega
      have hends : dualEnds z = (z, (z.1 - 1, z.2 - 1)) := by
        unfold dualEnds; unfold IsPrimal at hzp
        rw [ite_eq_right (by omega)]
      have hz' : ((z.1 - 1, z.2 - 1) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; unfold IsPrimal at *
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> push_cast at hn <;> omega
      obtain ⟨b, hb, hb2, hr⟩ := ih (z.1 - 1, z.2 - 1) hz' (by dsimp only; push_cast at hn; omega)
      refine ⟨b, hb, hb2, Relation.ReflTransGen.head ?_ hr⟩
      have := R.step_of_inner hm
      rw [hends] at this
      exact this
    · have hxz : z.1 = R.x0 := by omega
      have hm : (z.1 + 1, z.2) ∈ R.inner := by
        rw [mem_inner]; dsimp only; push_cast at hn; omega
      have hends : dualEnds (z.1 + 1, z.2) = (z, (z.1 + 1, z.2 - 1)) := by
        unfold dualEnds; unfold IsPrimal at hzp
        rw [ite_eq_left (by dsimp only; omega)]
        simp
      have hz' : ((z.1 + 1, z.2 - 1) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; unfold IsPrimal at *
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> push_cast at hn <;> omega
      obtain ⟨b, hb, hb2, hr⟩ := ih (z.1 + 1, z.2 - 1) hz' (by dsimp only; push_cast at hn; omega)
      refine ⟨b, hb, hb2, Relation.ReflTransGen.head ?_ hr⟩
      have := R.step_of_inner hm
      rw [hends] at this
      exact this


/-- Two bottom-row odd cells two apart are joined through the cell between them one row up. -/
theorem bottom_step (hh : 0 < R.h) {z : Cell} (hz : z ∈ R.dcells) (hzy : z.2 = R.y0)
    (hx : z.1 + 2 ≤ R.x0 + R.w) :
    Relation.ReflTransGen (StepRel dualEnds R.inner) z (z.1 + 2, z.2) := by
  have hzc := mem_cells.1 (mem_dcells.1 hz).1
  have hzp := (mem_dcells.1 hz).2
  have hh' : (0 : ℤ) < R.h := by exact_mod_cast hh
  unfold IsPrimal at hzp
  have hm1 : (z.1 + 1, z.2 + 1) ∈ R.inner := by rw [mem_inner]; dsimp only; omega
  have hm2 : (z.1 + 2, z.2 + 1) ∈ R.inner := by rw [mem_inner]; dsimp only; omega
  have e1 : dualEnds (z.1 + 1, z.2 + 1) = ((z.1 + 1, z.2 + 1), z) := by
    unfold dualEnds; rw [ite_eq_right (by dsimp only; omega)]
    ext <;> simp
  have e2 : dualEnds (z.1 + 2, z.2 + 1) = ((z.1 + 1, z.2 + 1), (z.1 + 2, z.2)) := by
    unfold dualEnds; rw [ite_eq_left (by dsimp only; omega)]
    ext <;> simp; ring
  have s1 := R.step_of_inner hm1
  have s2 := R.step_of_inner hm2
  rw [e1] at s1
  rw [e2] at s2
  exact (Relation.ReflTransGen.single (stepRel_symm s1)).tail s2

/-- The dual board graph (all inner edges) is connected. -/
theorem dual_connected (hw : 0 < R.w) (hh : 0 < R.h) {z z' : Cell} (hz : z ∈ R.dcells)
    (hz' : z' ∈ R.dcells) :
    Relation.ReflTransGen (StepRel dualEnds R.inner) z z' := by
  obtain ⟨b, hb, hby, hr⟩ := R.dual_to_bottom hw (z.2 - R.y0).toNat z hz (by
    have := mem_cells.1 (mem_dcells.1 hz).1; omega)
  obtain ⟨b', hb', hby', hr'⟩ := R.dual_to_bottom hw (z'.2 - R.y0).toNat z' hz' (by
    have := mem_cells.1 (mem_dcells.1 hz').1; omega)
  have hsymm : ∀ {x y : Cell}, Relation.ReflTransGen (StepRel dualEnds R.inner) x y →
      Relation.ReflTransGen (StepRel dualEnds R.inner) y x := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact (Relation.ReflTransGen.single (stepRel_symm hstep)).trans ih
  have hbb : ∀ n : ℕ, ∀ x y : Cell, x ∈ R.dcells → y ∈ R.dcells → x.2 = R.y0 → y.2 = R.y0 →
      (y.1 - x.1).natAbs = 2 * n →
      Relation.ReflTransGen (StepRel dualEnds R.inner) x y := by
    intro n
    induction n with
    | zero =>
      intro x y _ _ hx hy hn
      have : x = y := Prod.ext (by omega) (by omega)
      rw [this]
    | succ n ih =>
      intro x y hx hy hxy hyy hn
      have hxc := mem_cells.1 (mem_dcells.1 hx).1
      have hyc := mem_cells.1 (mem_dcells.1 hy).1
      have hxp := (mem_dcells.1 hx).2
      have hyp := (mem_dcells.1 hy).2
      unfold IsPrimal at hxp hyp
      by_cases hlt : x.1 < y.1
      · have hx2 : x.1 + 2 ≤ R.x0 + R.w := by omega
        have hmid : ((x.1 + 2, x.2) : Cell) ∈ R.dcells := by
          rw [mem_dcells, mem_cells]; unfold IsPrimal
          refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega
        exact (R.bottom_step hh hx hxy hx2).trans (ih _ y hmid hy (by dsimp only; omega) hyy
          (by dsimp only; omega))
      · have hgt : y.1 < x.1 := by omega
        have hy2 : y.1 + 2 ≤ R.x0 + R.w := by omega
        have hmid : ((y.1 + 2, y.2) : Cell) ∈ R.dcells := by
          rw [mem_dcells, mem_cells]; unfold IsPrimal
          refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega
        have := (R.bottom_step hh hy hyy hy2)
        have h2 := ih x (y.1 + 2, y.2) hx hmid hxy (by dsimp only; omega) (by dsimp only; omega)
        exact h2.trans (hsymm this)
  have hbc : Relation.ReflTransGen (StepRel dualEnds R.inner) b b' := by
    have hbp := (mem_dcells.1 hb).2
    have hbp' := (mem_dcells.1 hb').2
    unfold IsPrimal at hbp hbp'
    exact hbb ((b'.1 - b.1).natAbs / 2) b b' hb hb' hby hby' (by omega)
  exact hr.trans (hbc.trans (hsymm hr'))

end Rect

end PottsDiscontinuity.TorusCrossing
