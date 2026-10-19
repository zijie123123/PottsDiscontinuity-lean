module

public import PottsDiscontinuity.TorusTopology.RightwardPeriodicTurning
public import PottsDiscontinuity.TorusTopology.LatticeQuarterRotation

/-! Every actual simple periodic lattice curve has zero turn over a period. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Finset Planar.Medial

/-- The periodic discrete turning theorem, with an arbitrary nonzero deck vector. -/
theorem periodic_lattice_turn_eq_zero
    (f : ℕ → ℤ × ℤ) (hadj : ∀ n, FK.squareLattice.Adj (f n) (f (n+1)))
    (hf : Function.Injective f) (L : ℕ) (D : ℤ × ℤ) (hL : 0 < L)
    (hD : D ≠ (0,0)) (hper : ∀ n, f (n+L)=f n+D) :
    (∑ n ∈ range L, primalCompassQuarterTurn (sequenceCompass f hadj n)
      (sequenceCompass f hadj (n+1))) = 0 := by
  let f₁ := fun n => latticeQuarterRotation (f n)
  let f₂ := fun n => latticeQuarterRotation (f₁ n)
  let f₃ := fun n => latticeQuarterRotation (f₂ n)
  let D₁ := latticeQuarterRotation D
  let D₂ := latticeQuarterRotation D₁
  let D₃ := latticeQuarterRotation D₂
  have ha₁ : ∀ n, FK.squareLattice.Adj (f₁ n) (f₁ (n+1)) :=
    fun n => (latticeQuarterRotation_adj _ _).mpr (hadj n)
  have ha₂ : ∀ n, FK.squareLattice.Adj (f₂ n) (f₂ (n+1)) :=
    fun n => (latticeQuarterRotation_adj _ _).mpr (ha₁ n)
  have ha₃ : ∀ n, FK.squareLattice.Adj (f₃ n) (f₃ (n+1)) :=
    fun n => (latticeQuarterRotation_adj _ _).mpr (ha₂ n)
  have hi₁ : Function.Injective f₁ := latticeQuarterRotation_injective.comp hf
  have hi₂ : Function.Injective f₂ := latticeQuarterRotation_injective.comp hi₁
  have hi₃ : Function.Injective f₃ := latticeQuarterRotation_injective.comp hi₂
  have hp₁ : ∀ n, f₁ (n+L)=f₁ n+D₁ := by
    intro n; dsimp [f₁,D₁]; rw [hper,latticeQuarterRotation_add]
  have hp₂ : ∀ n, f₂ (n+L)=f₂ n+D₂ := by
    intro n; change latticeQuarterRotation (f₁ (n+L)) = _
    rw [hp₁,latticeQuarterRotation_add]
  have hp₃ : ∀ n, f₃ (n+L)=f₃ n+D₃ := by
    intro n; change latticeQuarterRotation (f₂ (n+L)) = _
    rw [hp₂,latticeQuarterRotation_add]
  have he₁ := sum_sequenceTurn_quarterRotation f hadj L
  have he₂ := sum_sequenceTurn_quarterRotation f₁ ha₁ L
  have he₃ := sum_sequenceTurn_quarterRotation f₂ ha₂ L
  have hpos : 0 < D.1 ∨ 0 < D₁.1 ∨ 0 < D₂.1 ∨ 0 < D₃.1 := by
    dsimp [D₁,D₂,D₃,latticeQuarterRotation]
    by_contra hn
    simp only [not_or,not_lt] at hn
    exact hD (Prod.ext (by omega) (by omega))
  rcases hpos with h0 | h1 | h2 | h3
  · exact periodic_lattice_turn_eq_zero_of_pos_horizontal f hadj hf L D hL h0 hper
  · have hz := periodic_lattice_turn_eq_zero_of_pos_horizontal f₁ ha₁ hi₁ L D₁ hL h1 hp₁
    exact he₁ ▸ hz
  · have hz := periodic_lattice_turn_eq_zero_of_pos_horizontal f₂ ha₂ hi₂ L D₂ hL h2 hp₂
    exact he₁ ▸ (he₂ ▸ hz)
  · have hz := periodic_lattice_turn_eq_zero_of_pos_horizontal f₃ ha₃ hi₃ L D₃ hL h3 hp₃
    exact he₁ ▸ (he₂ ▸ (he₃ ▸ hz))

end PottsDiscontinuity.TorusTopology
