module

public import PottsDiscontinuity.TorusTopology.LatticeSequenceWalk

/-! Orientation-preserving quarter rotation of actual lattice curves. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Planar.Medial

/-- Positive quarter rotation of the integer plane. -/
def latticeQuarterRotation (z : ℤ × ℤ) : ℤ × ℤ := (-z.2,z.1)

lemma latticeQuarterRotation_injective : Function.Injective latticeQuarterRotation := by
  intro u v h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [latticeQuarterRotation] at hx hy
  exact Prod.ext hy (by omega)

lemma latticeQuarterRotation_add (u v : ℤ × ℤ) :
    latticeQuarterRotation (u+v) = latticeQuarterRotation u+latticeQuarterRotation v := by
  ext <;> simp [latticeQuarterRotation]; ring

lemma latticeQuarterRotation_adj (u v : ℤ × ℤ) :
    FK.squareLattice.Adj (latticeQuarterRotation u) (latticeQuarterRotation v) ↔
      FK.squareLattice.Adj u v := by
  rw [FK.squareLattice_adj_iff,FK.squareLattice_adj_iff]
  dsimp [latticeQuarterRotation]
  omega

lemma squareDartCompass_quarterRotation {u v : ℤ × ℤ} (h : FK.squareLattice.Adj u v) :
    squareDartCompass ⟨⟨latticeQuarterRotation u,latticeQuarterRotation v⟩,
      (latticeQuarterRotation_adj u v).mpr h⟩ = squareDartCompass ⟨⟨u,v⟩,h⟩+1 := by
  have hh := (FK.squareLattice_adj_iff u v).mp h
  rcases hh with ⟨hx|hx,hy⟩ | ⟨hx,hy|hy⟩
  all_goals
    dsimp only [squareDartCompass,latticeQuarterRotation]
    simp only [neg_lt_neg_iff]
    split_ifs <;> norm_num <;> omega

lemma primalCompassQuarterTurn_add_one (a b : Fin 4) :
    primalCompassQuarterTurn (a+1) (b+1) = primalCompassQuarterTurn a b := by
  fin_cases a <;> fin_cases b <;> decide

lemma sequenceCompass_quarterRotation (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (n : ℕ) :
    sequenceCompass (fun n => latticeQuarterRotation (f n))
      (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) n =
      sequenceCompass f h n+1 := by
  exact squareDartCompass_quarterRotation (h n)

lemma sum_sequenceTurn_quarterRotation (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (L : ℕ) :
    (∑ n ∈ Finset.range L, primalCompassQuarterTurn
      (sequenceCompass (fun n => latticeQuarterRotation (f n))
        (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) n)
      (sequenceCompass (fun n => latticeQuarterRotation (f n))
        (fun n => (latticeQuarterRotation_adj _ _).mpr (h n)) (n+1))) =
    ∑ n ∈ Finset.range L, primalCompassQuarterTurn (sequenceCompass f h n)
      (sequenceCompass f h (n+1)) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [sequenceCompass_quarterRotation,sequenceCompass_quarterRotation,
    primalCompassQuarterTurn_add_one]

end PottsDiscontinuity.TorusTopology
