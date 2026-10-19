/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleSectorProfile

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The actual local quarter-turn at every vertex of one simple cycle is
controlled by the same orientation sign as its selected-face sector profile. -/
theorem parafermionicCoverSimpleCycleLocalTurning {n : ℕ}
    (hn : 1 ≤ n) {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle) :
    ∃ k : ℤ, (k = -1 ∨ k = 1) ∧
      ∀ (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support),
        parafermionicCoverPrimalCycleQuarterTurn p hp v hv =
          k * (2 -
            ((parafermionicCoverFiniteFaceSelectedIncidentVertices
              (parafermionicCoverSimpleCycleFillingSet hn p hp) v).card : ℤ)) := by
  obtain ⟨k, hk, hprofile⟩ := parafermionicCoverSimpleCycleSectorProfile hn p hp
  refine ⟨k, hk, ?_⟩
  intro v hv
  let din := parafermionicCoverPrimalCycleIncomingDirection p hp v hv
  let dout := parafermionicCoverPrimalCycleOutgoingDirection p hp v hv
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let Q := parafermionicCoverFiniteFaceSelectedCorners S v
  have hnonback : din ≠ dout + 2 := by
    simpa [din, dout] using
      parafermionicCoverPrimalCycleIncomingDirection_ne_outgoing_opposite p hp v hv
  have hdouble (d : Fin 4) : d + 2 + 2 = d := by
    fin_cases d <;> decide
  have hab : din + 2 ≠ dout := by
    intro h
    apply hnonback
    calc
      din = din + 2 + 2 := (hdouble din).symm
      _ = dout + 2 := by rw [h]
  have hlocal := primalCompassQuarterTurn_eq_sector_boundary_formula
    Q (din + 2) dout k hab hk (by
      intro d
      simpa [Q, S, din, dout] using hprofile v hv d)
  have hcard := parafermionicCoverFiniteFaceSelectedCorners_card S v
  change primalCompassQuarterTurn din dout =
    k * (2 -
      ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ))
  calc
    primalCompassQuarterTurn din dout =
        primalCompassQuarterTurn (din + 2 + 2) dout := by rw [hdouble]
    _ = k * (2 - (Q.card : ℤ)) := hlocal
    _ = k * (2 -
        ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ)) := by
      rw [parafermionicCoverFiniteFaceSelectedCorners_card]

end PottsDiscontinuity.TorusTopology.Planar.Medial
