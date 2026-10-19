module

public import Mathlib.Algebra.Order.Floor.Ring
public import PottsDiscontinuity.Torus.DiamondSeamWinding

/-! Integer potentials for horizontal cuts with no winding cycles. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus
variable {N M : ℕ}

/-- The integer horizontal-seam crossing coefficient. -/
def integerSeamCrossX (e : Fin N × Fin M) : ℤ :=
  if e.1.val=0 then (if checker e then -1 else 1) else 0

lemma integerSeamCrossX_cast (e : Fin N × Fin M) :
    (integerSeamCrossX e : ℚ)=diamondSeamCrossX e := by
  unfold integerSeamCrossX diamondSeamCrossX
  split_ifs <;> norm_num

/-- Flooring a rational potential preserves its integer edge increments. -/
theorem exists_int_horizontalPotential (hN : Even N) (hM : Even M)
    (A : RCConfig N M)
    (h : ∀ f : diamondCycleSpace hN hM A, diamondWindingX A f.val=0) :
    ∃ F : FaceVertex N M true → ℤ, ∀ e : OpenDiamondEdge A,
      F (faceEndpoint hN hM true e.val true) - F (faceEndpoint hN hM true e.val false) =
        integerSeamCrossX e.val := by
  obtain ⟨G,hG⟩ := exists_diamondPotential_of_cycle_annihilator hN hM A
    (fun e => diamondSeamCrossX e.val) h
  refine ⟨fun v => ⌊G v⌋,?_⟩
  intro e
  have he := congrFun hG e
  change G (faceEndpoint hN hM true e.val true) -
    G (faceEndpoint hN hM true e.val false) = diamondSeamCrossX e.val at he
  rw [← integerSeamCrossX_cast] at he
  have he' : G (faceEndpoint hN hM true e.val true) =
      G (faceEndpoint hN hM true e.val false) + (integerSeamCrossX e.val : ℚ) := by linarith
  change ⌊G (faceEndpoint hN hM true e.val true)⌋ -
    ⌊G (faceEndpoint hN hM true e.val false)⌋ = integerSeamCrossX e.val
  rw [he',Int.floor_add_intCast]
  omega

end PottsDiscontinuity.TorusExploration
