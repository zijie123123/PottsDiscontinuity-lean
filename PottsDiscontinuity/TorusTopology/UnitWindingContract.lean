module

public import PottsDiscontinuity.TorusTopology.UnitWindingHomology

/-! The corrected complete U=1 loop-homology structure for the torus correspondence
(Corollary 3.13). -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
variable {N M : ℕ}

/-- Exactly two homologically essential loops, of opposite classes (a,1) and
(-a,-1). The horizontal slope a need not be zero. -/
theorem U_one_loop_homology_structure
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (hU : rcVerticalWinding hN hM j A = 1) :
    ∃ (a : ℤ) (q₁ q₂ : Loop hN hM (rcSmoothing A)), q₁ ≠ q₂ ∧
      (∀ q, (loopVertical (checkerArrows N M) (rcSmoothing A)
          (checkerArrows_compatible hN hM _) j q ≠ 0 ∨
        loopSum (checkerArrows N M) (rcSmoothing A)
          (checkerArrows_compatible hN hM _) (horizontalCross i) q ≠ 0 ↔
          q = q₁ ∨ q = q₂)) ∧
      loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) j q₁ = 1 ∧
      loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) j q₂ = -1 ∧
      loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) (horizontalCross i) q₁ = a ∧
      loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) (horizontalCross i) q₂ = -a := by
  obtain ⟨q₁,q₂,hne,hs,h₁,h₂⟩ := U_one_vertical_loop_structure hN hM j A hU
  obtain ⟨a,ha⟩ := U_one_horizontal_multiple_vertical hN hM i j A hU
  refine ⟨a,q₁,q₂,hne,?_,h₁,h₂,?_,?_⟩
  · intro q
    rw [← hs]
    constructor
    · rintro (hv | hh)
      · exact hv
      · intro hv
        rw [ha,hv,mul_zero] at hh
        exact hh rfl
    · exact Or.inl
  · rw [ha,h₁,mul_one]
  · rw [ha,h₂,mul_neg_one]

/-- The source homological winding-loop count is exactly two in the U=1 sector. -/
theorem windingLoopCount_eq_two_of_U_eq_one
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (hU : rcVerticalWinding hN hM j A = 1) :
    windingLoopCount hN hM i j A = 2 := by
  classical
  obtain ⟨a,q₁,q₂,hne,hs,_⟩ := U_one_loop_homology_structure hN hM i j A hU
  have he : windingLoopSet hN hM i j A = {q₁,q₂} := by
    ext q
    simp only [windingLoopSet,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_insert,Finset.mem_singleton]
    exact hs q
  simp [windingLoopCount,he,hne]

end PottsDiscontinuity.TorusTopology
