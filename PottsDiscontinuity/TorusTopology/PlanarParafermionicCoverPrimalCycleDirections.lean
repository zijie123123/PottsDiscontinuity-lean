/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace/import relocation; direction choice is taken from explicitly proved unique existence. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverCompass
public import PottsDiscontinuity.TorusTopology.PlanarFiniteCompassFan
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

 theorem existsUniqueCompassDirection
    (u w : ParafermionicCoverVertex) (h : parafermionicCoverGraph.Adj u w) :
    ∃! d : Fin 4, w = parafermionicCoverCompassNeighbor u d := by
  obtain ⟨d,hd⟩ := (parafermionicCoverGraph_neighbor_iff_compassNeighbor u w).mp
    (by exact h)
  refine ⟨d,hd,?_⟩
  intro e he
  exact parafermionicCoverCompassNeighbor_injective u (he.symm.trans hd)

/-- The unique compass label of an actual directed edge of the full cover. -/
noncomputable def parafermionicCoverCompassDirection
    (u w : ParafermionicCoverVertex)
    (h : parafermionicCoverGraph.Adj u w) : Fin 4 :=
  Classical.choose
    (existsUniqueCompassDirection u w h).exists

theorem parafermionicCoverCompassDirection_neighbor
    (u w : ParafermionicCoverVertex)
    (h : parafermionicCoverGraph.Adj u w) :
    parafermionicCoverCompassNeighbor u
      (parafermionicCoverCompassDirection u w h) = w :=
  (Classical.choose_spec
    (existsUniqueCompassDirection u w h).exists).symm

theorem parafermionicCoverCompassDirection_reverse
    (u w : ParafermionicCoverVertex)
    (h : parafermionicCoverGraph.Adj u w) :
    parafermionicCoverCompassDirection w u h.symm =
      parafermionicCoverCompassDirection u w h + 2 := by
  have hforward := parafermionicCoverCompassDirection_neighbor u w h
  have hback0 := parafermionicCoverCompassNeighbor_reverse u
    (parafermionicCoverCompassDirection u w h)
  have hback :
      parafermionicCoverCompassNeighbor w
        (parafermionicCoverCompassDirection u w h + 2) = u := by
    calc
      parafermionicCoverCompassNeighbor w
          (parafermionicCoverCompassDirection u w h + 2) =
          parafermionicCoverCompassNeighbor
            (parafermionicCoverCompassNeighbor u
              (parafermionicCoverCompassDirection u w h))
            (parafermionicCoverCompassDirection u w h + 2) := by
              exact (congrArg (fun z => parafermionicCoverCompassNeighbor z
                (parafermionicCoverCompassDirection u w h + 2)) hforward).symm
      _ = u := hback0
  apply parafermionicCoverCompassNeighbor_injective w
  calc
    parafermionicCoverCompassNeighbor w
        (parafermionicCoverCompassDirection w u h.symm) = u :=
      parafermionicCoverCompassDirection_neighbor w u h.symm
    _ = parafermionicCoverCompassNeighbor w
        (parafermionicCoverCompassDirection u w h + 2) := hback.symm

private theorem parafermionicCoverPrimalCycleRotate_isCycle {n : ℕ}
    {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) :
    (p.rotate v hv).IsCycle := by
  simpa using hp.rotate hv

private theorem parafermionicCoverPrimalCycleRotate_not_nil {n : ℕ}
    {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) :
    ¬ (p.rotate v hv).Nil := by
  have hlen := (parafermionicCoverPrimalCycleRotate_isCycle p hp v hv).three_le_length
  exact (SimpleGraph.Walk.not_nil_iff_lt_length).2 (by omega)

/-- The actual closed walk rotated to begin at `v`. -/
def parafermionicCoverPrimalCycleRotate {n : ℕ}
    {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) :=
  p.rotate v hv

/-- Incoming travel direction at `v`, read from the penultimate vertex of the
same rotated actual cycle. -/
noncomputable def parafermionicCoverPrimalCycleIncomingDirection {n : ℕ}
    {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) : Fin 4 :=
  let r := parafermionicCoverPrimalCycleRotate p v hv
  parafermionicCoverCompassDirection r.penultimate.1 v.1 (by
    have hadj := r.adj_penultimate (parafermionicCoverPrimalCycleRotate_not_nil p hp v hv)
    change parafermionicCoverGraph.Adj r.penultimate.1 v.1 at hadj
    exact hadj)

/-- Outgoing travel direction at `v`, read from the second vertex of the same
rotated actual cycle. -/
noncomputable def parafermionicCoverPrimalCycleOutgoingDirection {n : ℕ}
    {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) : Fin 4 :=
  let r := parafermionicCoverPrimalCycleRotate p v hv
  parafermionicCoverCompassDirection v.1 r.snd.1 (by
    have hadj := r.adj_snd (parafermionicCoverPrimalCycleRotate_not_nil p hp v hv)
    change parafermionicCoverGraph.Adj v.1 r.snd.1 at hadj
    exact hadj)

/-- The incoming direction names the actual preceding vertex in the rotated
cycle. -/
theorem parafermionicCoverPrimalCycleIncomingDirection_neighbor {n : ℕ}
    {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverPrimalCycleRotate p v hv).penultimate.1
      (parafermionicCoverPrimalCycleIncomingDirection p hp v hv) = v.1 := by
  let r := parafermionicCoverPrimalCycleRotate p v hv
  have hadj := r.adj_penultimate (parafermionicCoverPrimalCycleRotate_not_nil p hp v hv)
  change parafermionicCoverGraph.Adj r.penultimate.1 v.1 at hadj
  simpa [parafermionicCoverPrimalCycleIncomingDirection, r,
    parafermionicCoverPrimalCycleRotate] using
      parafermionicCoverCompassDirection_neighbor r.penultimate.1 v.1 hadj

/-- The outgoing direction names the actual next vertex in the rotated cycle. -/
theorem parafermionicCoverPrimalCycleOutgoingDirection_neighbor {n : ℕ}
    {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) :
    parafermionicCoverCompassNeighbor v.1
      (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv) =
        (parafermionicCoverPrimalCycleRotate p v hv).snd.1 := by
  let r := parafermionicCoverPrimalCycleRotate p v hv
  have hadj := r.adj_snd (parafermionicCoverPrimalCycleRotate_not_nil p hp v hv)
  change parafermionicCoverGraph.Adj v.1 r.snd.1 at hadj
  simpa [parafermionicCoverPrimalCycleOutgoingDirection, r,
    parafermionicCoverPrimalCycleRotate] using
      parafermionicCoverCompassDirection_neighbor v.1 r.snd.1 hadj

/-- The local quarter-turn attached to the two actual travel directions at a
vertex of a simple closed walk. -/
noncomputable def parafermionicCoverPrimalCycleQuarterTurn {n : ℕ}
    {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) : ℤ :=
  primalCompassQuarterTurn
    (parafermionicCoverPrimalCycleIncomingDirection p hp v hv)
    (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv)

/-- A simple closed walk cannot immediately reverse at the chosen vertex. -/
theorem parafermionicCoverPrimalCycleIncomingDirection_ne_outgoing_opposite
    {n : ℕ} {x : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk x x) (hp : p.IsCycle)
    (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) :
    parafermionicCoverPrimalCycleIncomingDirection p hp v hv ≠
      parafermionicCoverPrimalCycleOutgoingDirection p hp v hv + 2 := by
  let r := parafermionicCoverPrimalCycleRotate p v hv
  let din := parafermionicCoverPrimalCycleIncomingDirection p hp v hv
  let dout := parafermionicCoverPrimalCycleOutgoingDirection p hp v hv
  intro hbad
  have hrel : dout = din + 2 := by
    have hdouble (d : Fin 4) : d + 2 + 2 = d := by fin_cases d <;> decide
    calc
      dout = dout + 2 + 2 := (hdouble dout).symm
      _ = din + 2 := by rw [← hbad]
  have hprevAdj := r.adj_penultimate
    (parafermionicCoverPrimalCycleRotate_not_nil p hp v hv)
  change parafermionicCoverGraph.Adj r.penultimate.1 v.1 at hprevAdj
  have hreverseDir :
      parafermionicCoverCompassDirection v.1 r.penultimate.1 hprevAdj.symm = din + 2 := by
    simpa [din, parafermionicCoverPrimalCycleIncomingDirection,
      parafermionicCoverPrimalCycleRotate, r] using
        parafermionicCoverCompassDirection_reverse r.penultimate.1 v.1 hprevAdj
  have hreverse := parafermionicCoverCompassDirection_neighbor
    v.1 r.penultimate.1 hprevAdj.symm
  have hout := parafermionicCoverPrimalCycleOutgoingDirection_neighbor p hp v hv
  have hvertices : r.snd = r.penultimate := by
    apply Subtype.ext
    calc
      r.snd.1 = parafermionicCoverCompassNeighbor v.1 dout := hout.symm
      _ = parafermionicCoverCompassNeighbor v.1
          (parafermionicCoverCompassDirection v.1 r.penultimate.1 hprevAdj.symm) := by
            rw [hreverseDir, hrel]
      _ = r.penultimate.1 := hreverse
  exact (parafermionicCoverPrimalCycleRotate_isCycle p hp v hv).snd_ne_penultimate hvertices

end PottsDiscontinuity.TorusTopology.Planar.Medial
