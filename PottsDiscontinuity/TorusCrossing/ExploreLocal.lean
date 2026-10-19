module

public import PottsDiscontinuity.TorusCrossing.BdConn
public import PottsDiscontinuity.TorusCrossing.Local

/-!
# Local structure of the exploration at primal cells

For an exploration of a board `R` (port rows `p₁` the source row and `p₂` the opposite row):
every corner edge of a primal cell on the row `p₁` is explored; a corner edge of a primal cell
on the row `p₂` is a boundary edge as soon as it is explored; and a primal cell seeing both an
explored and an unexplored edge sees a boundary edge.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable {R : Rect}

theorem mem_expRm_iff {p₁ p₂ : ℤ} {A : Finset Cell} {m : Cell} :
    m ∈ R.expRm p₁ p₂ A ↔ m ∈ R.inner ∧
      ¬ ((dualEnds m).1 ∈ R.expU p₁ p₂ A ∧ (dualEnds m).2 ∈ R.expU p₁ p₂ A) := by
  unfold expRm expX
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    rintro ⟨h1, h2⟩
    rcases h with h | h
    · exact (Finset.mem_sdiff.1 h).2 h1
    · exact (Finset.mem_sdiff.1 h).2 h2
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    have hmem := R.dData.mem m hm
    by_cases h1 : (dualEnds m).1 ∈ R.expU p₁ p₂ A
    · right
      exact Finset.mem_sdiff.2 ⟨hmem.2, fun h2 => h ⟨h1, h2⟩⟩
    · left
      exact Finset.mem_sdiff.2 ⟨hmem.1, h1⟩

theorem mem_unexplored_iff {p₁ p₂ : ℤ} {A : Finset Cell} {m : Cell} :
    (m ∈ R.inner ∧ m ∉ R.expRm p₁ p₂ A) ↔ m ∈ R.inner ∧
      ((dualEnds m).1 ∈ R.expU p₁ p₂ A ∧ (dualEnds m).2 ∈ R.expU p₁ p₂ A) := by
  rw [mem_expRm_iff]
  constructor
  · rintro ⟨hm, h⟩
    exact ⟨hm, by_contra fun h' => h ⟨hm, h'⟩⟩
  · rintro ⟨hm, h⟩
    exact ⟨hm, fun h' => h'.2 h⟩

/-- Every corner of a primal cell has a dual end in the row of the cell. -/
theorem corner_dual_row (c : Cell) (hc : IsPrimal c) {e : Cell} (he : e ∈ corners c) :
    ∃ z, (z = (dualEnds e).1 ∨ z = (dualEnds e).2) ∧ z.2 = c.2 := by
  have c1 := dualEnds_corner1 c hc
  have c2 := dualEnds_corner2 c hc
  have c3 := dualEnds_corner3 c hc
  have c4 := dualEnds_corner4 c hc
  unfold corners at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h | h <;> rw [h]
  · rw [c1]; exact ⟨(c.1 - 1, c.2), Or.inl rfl, rfl⟩
  · rw [c2]; exact ⟨(c.1 + 1, c.2), Or.inl rfl, rfl⟩
  · rw [c3]; exact ⟨(c.1 - 1, c.2), Or.inr rfl, rfl⟩
  · rw [c4]; exact ⟨(c.1 + 1, c.2), Or.inr rfl, rfl⟩

theorem corner_expRm_of_row_p1 {p₁ p₂ : ℤ} {A : Finset Cell} {c e : Cell} (hc : c ∈ R.pcells)
    (hcr : c.2 = p₁) (he : e ∈ corners c) (hein : e ∈ R.inner) :
    e ∈ R.expRm p₁ p₂ A := by
  obtain ⟨z, hz, hzr⟩ := corner_dual_row c (Rect.mem_pcells.1 hc).2 he
  have hzc : z ∈ R.dcells := by
    have := R.dData.mem e hein
    rcases hz with rfl | rfl
    · exact this.1
    · exact this.2
  have hzD : z ∈ R.expD p₁ A := R.mem_expD_of_faceRow (R.faceRow_mem.2 ⟨hzc, by omega⟩)
  rw [mem_expRm_iff]
  refine ⟨hein, fun h => ?_⟩
  rcases hz with rfl | rfl
  · exact expU_subset_not_expD h.1 hzD
  · exact expU_subset_not_expD h.2 hzD

theorem corner_expBd_of_row_p2 {p₁ p₂ : ℤ} {A : Finset Cell}
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) {c e : Cell} (hc : c ∈ R.pcells)
    (hcr : c.2 = p₂) (he : e ∈ corners c) (hein : e ∈ R.inner) (hex : e ∈ R.expRm p₁ p₂ A) :
    e ∈ R.expBd p₁ p₂ A := by
  obtain ⟨z, hz, hzr⟩ := corner_dual_row c (Rect.mem_pcells.1 hc).2 he
  have hzc : z ∈ R.dcells := by
    have := R.dData.mem e hein
    rcases hz with rfl | rfl
    · exact this.1
    · exact this.2
  have hzU : z ∈ R.expU p₁ p₂ A := R.mem_expU_of_faceRow hb (R.faceRow_mem.2 ⟨hzc, by omega⟩)
  rw [mem_expRm_iff] at hex
  rw [R.mem_expBd_iff]
  refine ⟨hein, ?_⟩
  unfold IsSep
  change ((dualEnds e).1 ∈ R.expU p₁ p₂ A ↔ ¬ (dualEnds e).2 ∈ R.expU p₁ p₂ A)
  rcases hz with rfl | rfl
  · exact ⟨fun _ h2 => hex.2 ⟨hzU, h2⟩, fun _ => hzU⟩
  · exact ⟨fun h1 _ => hex.2 ⟨h1, hzU⟩, fun h => absurd hzU h⟩

/-- A primal cell seeing an explored and an unexplored edge sees a boundary edge. -/
theorem vex_vun (hh : 0 < R.h) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) (Qinn : Finset Cell)
    (hamb : ∀ c ∈ R.pcells, c.2 ≠ p₂ → ∀ e ∈ corners c, e ∈ Qinn → e ∈ R.inner)
    {c : Cell} (hc : c ∈ R.pcells)
    (h1 : ∃ e ∈ corners c, e ∈ R.expRm p₁ p₂ A)
    (h2 : ∃ e ∈ corners c, e ∈ Qinn ∧ e ∉ R.expRm p₁ p₂ A) :
    ∃ e ∈ corners c, e ∈ R.expBd p₁ p₂ A := by
  have hh' : (0 : ℤ) < R.h := by exact_mod_cast hh
  obtain ⟨e, he, hex⟩ := h1
  obtain ⟨e', he', hQ, hne'⟩ := h2
  have hexin : e ∈ R.inner := ((mem_expRm_iff).1 hex).1
  by_cases hc2 : c.2 = p₂
  · exact ⟨e, he, corner_expBd_of_row_p2 hb hc hc2 he hexin hex⟩
  · have he'in : e' ∈ R.inner := hamb c hc hc2 e' he' hQ
    by_cases hc1 : c.2 = p₁
    · exact absurd (corner_expRm_of_row_p1 (A := A) (p₂ := p₂) hc hc1 he' he'in) hne'
    · have hcc := Rect.mem_pcells.1 hc
      obtain ⟨e'', he'', hein'', hsep⟩ := local_vbd R (fun z => z ∈ R.expU p₁ p₂ A) c hcc.2 hcc.1
        (fun h => by omega) (fun h => by omega)
        ⟨e, he, hexin, ((mem_expRm_iff).1 hex).2⟩
        ⟨e', he', he'in, ((mem_unexplored_iff).1 ⟨he'in, hne'⟩).2⟩
      exact ⟨e'', he'', (R.mem_expBd_iff).2 ⟨hein'', hsep⟩⟩

end Rect

end PottsDiscontinuity.TorusCrossing
