module

public import PottsDiscontinuity.Torus.LoopOrientation

/-!
# All loop orientations, with no existence choices

Choosing one Boolean per canonical cyclic loop reconstructs an arrow field compatible
with the given smoothing. The construction and its inverse are proved explicitly.
Thus there really are exactly two independent orientations per smoothed loop.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}
variable (ω₀ : ArrowConfig N M) (s : Smoothing N M) (h₀ : CompatibleConfig ω₀ s)

/-- Orient each edge according to the Boolean attached to its canonical loop. -/
def orientArrows (F : DirectedLoop ω₀ s h₀ → Bool) : ArrowConfig N M where
  horiz v := if ω₀.horiz v then F (loopOfDart ω₀ s h₀ (v, .east))
    else !F (loopOfDart ω₀ s h₀ (v, .east))
  vert v := if ω₀.vert v then F (loopOfDart ω₀ s h₀ (v, .north))
    else !F (loopOfDart ω₀ s h₀ (v, .north))

/-- The reconstructed orientation, evaluated on any edge slot. -/
theorem dartOut_orientArrows (F : DirectedLoop ω₀ s h₀ → Bool) (d : Dart N M) :
    dartOut (orientArrows ω₀ s h₀ F) d =
      if dartOut ω₀ d then F (loopOfDart ω₀ s h₀ d) else !F (loopOfDart ω₀ s h₀ d) := by
  have hb : ∀ a b : Bool, Bool.not (if a then b else !b) = (if !a then b else !b) := by decide
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p with
  | east => rfl
  | north => rfl
  | west =>
    have hq : loopOfDart ω₀ s h₀ ((prv i, j), .east) =
        loopOfDart ω₀ s h₀ ((i, j), .west) :=
      loopOfDart_edgeReverse ω₀ s h₀ ((i, j), .west)
    simp only [dartOut, localOut, ArrowConfig.left, orientArrows, hq]
    exact hb _ _
  | south =>
    have hq : loopOfDart ω₀ s h₀ ((i, prv j), .north) =
        loopOfDart ω₀ s h₀ ((i, j), .south) :=
      loopOfDart_edgeReverse ω₀ s h₀ ((i, j), .south)
    simp only [dartOut, localOut, ArrowConfig.below, orientArrows, hq]
    exact hb _ _

/-- Independent loop reversals preserve every local in-to-out strand pairing. -/
theorem orientArrows_compatible (F : DirectedLoop ω₀ s h₀ → Bool) :
    CompatibleConfig (orientArrows ω₀ s h₀ F) s := by
  have hlocal : ∀ b l r d u : Bool,
      (∀ p : Port, localOut l r d u (pairedPort b p) = !localOut l r d u p) →
        Compatible b l r d u := by decide
  intro v
  apply hlocal
  intro p
  have hd : dartOut (orientArrows ω₀ s h₀ F) (strandReverse s (v, p)) =
      !dartOut (orientArrows ω₀ s h₀ F) (v, p) := by
    rw [dartOut_orientArrows, dartOut_orientArrows,
      loopOfDart_strandReverse, dartOut_strandReverse h₀]
    have hb : ∀ a b : Bool, (if !a then b else !b) = Bool.not (if a then b else !b) := by decide
    exact hb _ _
  exact hd

/-- Encoding recovers every prescribed loop orientation. -/
theorem loopOrientation_orientArrows (F : DirectedLoop ω₀ s h₀ → Bool) :
    loopOrientation ω₀ s h₀ (orientArrows ω₀ s h₀ F)
      (orientArrows_compatible ω₀ s h₀ F) = F := by
  funext q
  refine Quotient.inductionOn q ?_
  intro d
  change dartOut (orientArrows ω₀ s h₀ F) d.val = F (directedLoopOf ω₀ s h₀ d)
  rw [dartOut_orientArrows]
  simp only [d.property, ite_true]
  rw [loopOfDart_of_out ω₀ s h₀ d.val d.property]

/-- Decoding the orientation of a compatible arrow field recovers all of its arrows. -/
theorem orientArrows_loopOrientation (ω : ArrowConfig N M) (h : CompatibleConfig ω s) :
    orientArrows ω₀ s h₀ (loopOrientation ω₀ s h₀ ω h) = ω := by
  apply ArrowConfig.ext
  · funext v
    exact (dartOut_eq_loopOrientation ω₀ s h₀ ω h (v, .east)).symm
  · funext v
    exact (dartOut_eq_loopOrientation ω₀ s h₀ ω h (v, .north)).symm

/-- Compatible arrow fields are precisely independent Boolean orientations of the loops. -/
def orientationEquiv : {ω : ArrowConfig N M // CompatibleConfig ω s} ≃
    (DirectedLoop ω₀ s h₀ → Bool) where
  toFun x := loopOrientation ω₀ s h₀ x.val x.property
  invFun F := ⟨orientArrows ω₀ s h₀ F, orientArrows_compatible ω₀ s h₀ F⟩
  left_inv x := Subtype.ext (orientArrows_loopOrientation ω₀ s h₀ x.val x.property)
  right_inv := loopOrientation_orientArrows ω₀ s h₀

end PottsDiscontinuity.Torus
