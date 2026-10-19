module

public import PottsDiscontinuity.TorusTopology.SquareLatticeTurning

/-! Actual finite walks traced by a unit-step lattice sequence. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph

/-- The actual compass direction of a sequence's nth unit edge. -/
def sequenceCompass (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (n : ℕ) : Fin 4 :=
  squareDartCompass ⟨⟨f n,f (n+1)⟩,h n⟩

/-- Traverse the first n edges of the given actual nearest-neighbor sequence. -/
def latticeSequenceWalk (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) :
    (n : ℕ) → FK.squareLattice.Walk (f 0) (f n)
  | 0 => .nil
  | n+1 => (latticeSequenceWalk f h n).concat (h n)

@[simp] lemma latticeSequenceWalk_length (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (n : ℕ) :
    (latticeSequenceWalk f h n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [latticeSequenceWalk,ih]

lemma latticeSequenceWalk_support (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (n : ℕ) :
    (latticeSequenceWalk f h n).support = (List.range (n+1)).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [latticeSequenceWalk,Walk.support_concat,ih,List.range_succ,
      List.map_append,List.map_singleton]

lemma latticeSequenceWalk_isPath (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (hf : Function.Injective f) (n : ℕ) :
    (latticeSequenceWalk f h n).IsPath := by
  rw [Walk.isPath_def,latticeSequenceWalk_support]
  exact List.nodup_range.map hf

lemma latticeSequenceWalk_compassDirections (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (n : ℕ) :
    squareWalkCompassDirections (latticeSequenceWalk f h n) =
      (List.range n).map (sequenceCompass f h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [latticeSequenceWalk,squareWalkCompassDirections,Walk.darts_concat,
      List.concat_eq_append,List.map_append,List.map_singleton]
    change squareWalkCompassDirections (latticeSequenceWalk f h n) ++ _ = _
    rw [ih,List.range_succ,List.map_append,List.map_singleton]
    rfl

lemma sequenceCompass_periodic (f : ℕ → ℤ × ℤ)
    (h : ∀ n, FK.squareLattice.Adj (f n) (f (n+1))) (L : ℕ) (D : ℤ × ℤ)
    (hp : ∀ n, f (n+L) = f n+D) (n : ℕ) :
    sequenceCompass f h (n+L) = sequenceCompass f h n := by
  dsimp only [sequenceCompass,squareDartCompass]
  simp only [show n+L+1 = n+1+L by omega,hp,Prod.fst_add,Prod.snd_add,add_lt_add_iff_right]

end PottsDiscontinuity.TorusTopology
