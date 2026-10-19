module

public import PottsDiscontinuity.TorusLoops.FiniteEnergy
public import PottsDiscontinuity.TorusRC.ReflectionGraph

/-! # Reflection symmetry of the exact indexed torus law -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

private theorem stateCount_reflect (hMp : 0 < M) (t : ℤ) (A : RCConfig N M) (b : Bool) :
    (Finset.univ.filter (fun e => reflectRCConfig hMp t A e = b)).card =
      (Finset.univ.filter (fun e => A e = b)).card := by
  classical
  apply Finset.card_bij (fun e _ => reflectEdgeIndex hMp t e)
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩
  · intro a _ b _ hab
    exact (reflectEdgeIndex hMp t).injective hab
  · intro e he
    refine ⟨reflectEdgeIndex hMp t e, ?_, reflectEdgeIndex_involutive hMp t e⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by
      simpa only [reflectRCConfig, reflectEdgeIndex_involutive hMp t e] using
        (Finset.mem_filter.mp he).2⟩

theorem torusRCWeight_reflect (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (t : ℤ) (ht : Even t)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCWeight hN hM q (reflectRCConfig hMp t A) = torusRCWeight hN hM q A := by
  rw [torusRCWeight, torusRCWeight, openCount, closedCount,
    stateCount_reflect hMp t A true, stateCount_reflect hMp t A false,
    clusterCount_reflect hN hM hNp hMp t ht]
  rfl

def reflectRCConfigEquiv (hMp : 0 < M) (t : ℤ) : RCConfig N M ≃ RCConfig N M where
  toFun := reflectRCConfig hMp t
  invFun := reflectRCConfig hMp t
  left_inv := reflectRCConfig_involutive hMp t
  right_inv := reflectRCConfig_involutive hMp t

theorem torusRCMass_reflect (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (t : ℤ) (ht : Even t)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCMass hN hM q (reflectRCConfig hMp t A) = torusRCMass hN hM q A := by
  unfold torusRCMass
  rw [torusRCWeight_reflect hN hM hNp hMp t ht]

/-- The normalized indexed-edge probability is invariant under an actual
horizontal reflection; no simple-graph approximation is involved. -/
theorem torusRCProbability_reflect (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (t : ℤ) (ht : Even t)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q E =
      torusRCProbability hN hM q (reflectRCConfig hMp t ⁻¹' E) := by
  classical
  rw [torusRCProbability_eq_sum, torusRCProbability_eq_sum]
  calc
    _ = ∑ A, E.indicator (torusRCMass hN hM q) (reflectRCConfigEquiv hMp t A) :=
      (Equiv.sum_comp (reflectRCConfigEquiv hMp t)
        (E.indicator (torusRCMass hN hM q))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      change (if reflectRCConfig hMp t A ∈ E then
        torusRCMass hN hM q (reflectRCConfig hMp t A) else 0) =
        (if reflectRCConfig hMp t A ∈ E then torusRCMass hN hM q A else 0)
      rw [torusRCMass_reflect hN hM hNp hMp t ht]

end PottsDiscontinuity.TorusRC
