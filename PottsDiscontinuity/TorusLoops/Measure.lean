module

public import PottsDiscontinuity.TorusRC.MeasureFacts

/-!
# The finite critical random-cluster law on the diamond torus

This module re-exports the normalization of the indexed `torusRCWeight` built in `TorusRC/`
as the paper's torus law `φ_T`. The finite sample space retains indexed edges,
including multiplicities at small periods.
-/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The normalized critical torus random-cluster measure `φ_T`. -/
noncomputable abbrev phi_T (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) :
    Measure (RCConfig N M) :=
  PottsDiscontinuity.TorusRC.torusRCMeasure hN hM q

/-- Real-valued probability of an event under `φ_T`. -/
noncomputable abbrev phi_T_probability (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) : ℝ :=
  PottsDiscontinuity.TorusRC.torusRCProbability hN hM q E

@[simp] theorem phi_T_singleton (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    phi_T hN hM q {A} = ENNReal.ofReal
      (PottsDiscontinuity.TorusRC.torusRCMass hN hM q A) :=
  PottsDiscontinuity.TorusRC.torusRCMeasure_singleton hN hM q A

@[simp] theorem phi_T_probability_singleton (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    phi_T_probability hN hM q {A} =
      PottsDiscontinuity.TorusRC.torusRCMass hN hM q A :=
  PottsDiscontinuity.TorusRC.torusRCProbability_singleton hN hM q A

theorem phi_T_probability_eq_sum (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    phi_T_probability hN hM q E =
      ∑ A, E.indicator (PottsDiscontinuity.TorusRC.torusRCMass hN hM q) A :=
  PottsDiscontinuity.TorusRC.torusRCProbability_eq_sum hN hM q E

end PottsDiscontinuity.TorusLoops
