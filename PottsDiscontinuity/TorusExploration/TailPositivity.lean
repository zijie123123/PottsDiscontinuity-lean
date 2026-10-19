module

public import PottsDiscontinuity.Torus.WindingReorientation
public import PottsDiscontinuity.TorusRC.ElementaryTail

/-! Nonempty winding-tail events in the widths needed for logarithmic estimates. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusRC PottsDiscontinuity.SixVertex
variable {N M : ℕ}

/-- A literal ice configuration with every horizontal and vertical arrow
pointing in the negative coordinate direction. -/
def negativeArrows (N M : ℕ) : ArrowConfig N M := ⟨fun _ => false,fun _ => false⟩

lemma negativeArrows_ice : (negativeArrows N M).IceRule := by
  intro v
  rfl

lemma negativeArrows_absUp : (negativeArrows N M).absUp=0 := by
  unfold ArrowConfig.absUp
  split_ifs <;> simp [ArrowConfig.rowUp,negativeArrows]

/-- Every winding tail below half the width has an actual indexed configuration. -/
theorem windingTail_nonempty (hN : Even N) (hM : Even M) (j : Fin M)
    (r : ℕ) (hr : r ≤ N/2) :
    (torusRCVerticalTail hN hM j r).Nonempty := by
  obtain ⟨s,hs⟩ := (exists_compatibleConfig_iff (negativeArrows N M)).2 negativeArrows_ice
  let A := smoothingRC s
  have hA : CompatibleConfig (negativeArrows N M) (rcSmoothing A) := by
    simpa only [A,rcSmoothing_smoothingRC] using hs
  have hU := sector_le_rcVerticalWinding hN hM j A (negativeArrows N M) hA
    (r := N/2) (by rw [negativeArrows_absUp,zero_add])
  exact ⟨A,hr.trans hU⟩

/-- The real logarithm in the winding-tail rate is taken at a positive number
once the width is at least twice the requested winding. -/
theorem windingTail_probability_pos (hN : Even N) (hM : Even M) (j : Fin M)
    (q : Set.Ici (1 : ℝ)) (r : ℕ) (hr : r ≤ N/2) :
    0 < torusRCProbability hN hM q (torusRCVerticalTail hN hM j r) := by
  obtain ⟨A,hA⟩ := windingTail_nonempty hN hM j r hr
  have hm := torusRCProbability_mono hN hM q
    (show {A} ⊆ torusRCVerticalTail hN hM j r from Set.singleton_subset_iff.2 hA)
  rw [torusRCProbability_singleton] at hm
  exact (torusRCMass_pos hN hM q A).trans_le hm

end PottsDiscontinuity.TorusExploration
