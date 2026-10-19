/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: namespace/import relocation; generic walk API only.
Generic compass definitions are copied from the same source. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleTurning
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverWalkFiniteBox

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open Classical

/-- The ordered compass labels of the actual directed darts of a full-cover walk. -/
noncomputable def parafermionicCoverWalkCompassDirections {u v : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v) : List (Fin 4) :=
  p.darts.map fun d => parafermionicCoverCompassDirection d.fst d.snd d.adj

@[simp] theorem parafermionicCoverWalkCompassDirections_nil (u : ParafermionicCoverVertex) :
    parafermionicCoverWalkCompassDirections (Walk.nil : parafermionicCoverGraph.Walk u u) = [] := by
  simp [parafermionicCoverWalkCompassDirections]

@[simp] theorem parafermionicCoverWalkCompassDirections_cons
    {u v w : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v)
    (p : parafermionicCoverGraph.Walk v w) :
    parafermionicCoverWalkCompassDirections (Walk.cons h p) =
      parafermionicCoverCompassDirection u v h ::
        parafermionicCoverWalkCompassDirections p := by
  simp [parafermionicCoverWalkCompassDirections]

@[simp] theorem parafermionicCoverWalkCompassDirections_append
    {u v w : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v)
    (q : parafermionicCoverGraph.Walk v w) :
    parafermionicCoverWalkCompassDirections (p.append q) =
      parafermionicCoverWalkCompassDirections p ++
        parafermionicCoverWalkCompassDirections q := by
  simp [parafermionicCoverWalkCompassDirections]

theorem parafermionicCoverCompassDirection_eq_of_neighbor
    {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) (d : Fin 4)
    (hd : parafermionicCoverCompassNeighbor u d = v) :
    parafermionicCoverCompassDirection u v h = d := by
  apply parafermionicCoverCompassNeighbor_injective u
  calc
    parafermionicCoverCompassNeighbor u
        (parafermionicCoverCompassDirection u v h) = v :=
      parafermionicCoverCompassDirection_neighbor u v h
    _ = parafermionicCoverCompassNeighbor u d := hd.symm

/-- The cyclic compass turn of an actual full-cover closed walk, including the
last-to-first dart pair. -/
noncomputable def parafermionicCoverWalkCyclicCompassTurn
    {u : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u u) : ℤ :=
  ((parafermionicCoverWalkCompassDirections p).zipWith
    primalCompassQuarterTurn
    ((parafermionicCoverWalkCompassDirections p).rotate 1)).sum

@[simp] theorem parafermionicCoverWalkCyclicCompassTurn_nil
    (u : ParafermionicCoverVertex) :
    parafermionicCoverWalkCyclicCompassTurn
      (Walk.nil : parafermionicCoverGraph.Walk u u) = 0 := by
  simp [parafermionicCoverWalkCyclicCompassTurn]

/-- Mapping an actual finite-box walk into the full cover preserves the exact
ordered compass label of every dart. -/

private theorem parafermionicCoverWalk_rotate_dart_fst_eq_snd
    {V : Type*} {G : SimpleGraph V} {u : V} (p : G.Walk u u) :
    (p.darts.map fun d => d.toProd.1).rotate 1 =
      p.darts.map fun d => d.toProd.2 := by
  cases p with
  | nil => simp
  | @cons a b c h q =>
      simp only [Walk.darts_cons, List.map_cons]
      rw [List.rotate_cons_succ]
      simp only [List.rotate_zero]
      have hfst := Walk.map_fst_darts_append q
      have hsnd := Walk.cons_map_snd_darts q
      rw [hfst, hsnd]

private theorem parafermionicCover_mem_zip_endpoint_eq
    {α β : Type*} (L R : List α) (fst snd : α → β)
    (hrot : R.map fst = L.map snd)
    {d e : α} (hmem : (d, e) ∈ L.zip R) : snd d = fst e := by
  induction L generalizing R with
  | nil => simp at hmem
  | cons a L ih =>
      cases R with
      | nil => simp at hmem
      | cons b R =>
          simp only [List.map_cons, List.cons.injEq] at hrot
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · rcases hhead with ⟨rfl, rfl⟩
            exact hrot.1.symm
          · exact ih R hrot.2 htail

private theorem parafermionicCoverDart_snd_injective_of_isCycle
    {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle)
    {d e : G.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts)
    (h : d.snd = e.snd) : d = e := by
  have hmap : (p.darts.map fun x => x.snd).Nodup := by
    rw [Walk.map_snd_darts]
    exact hp.support_nodup
  have hnodup : p.darts.Nodup := List.Nodup.of_map (fun x => x.snd) hmap
  have hinj := (List.nodup_map_iff_inj_on hnodup).mp hmap
  exact hinj d hd e he h

private theorem parafermionicCoverDart_fst_injective_of_isCycle
    {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle)
    {d e : G.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts)
    (h : d.fst = e.fst) : d = e := by
  have hrev : p.reverse.IsCycle := hp.reverse
  have hd' : d.symm ∈ p.reverse.darts := by simpa using hd
  have he' : e.symm ∈ p.reverse.darts := by simpa using he
  have h' : d.symm.snd = e.symm.snd := h
  have := parafermionicCoverDart_snd_injective_of_isCycle p.reverse hrev hd' he' h'
  simpa using congrArg Dart.symm this

private theorem parafermionicCoverPrimalCycle_pair_turn_eq_local
    {n : ℕ} {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    {d e : (parafermionicCoverBoxGraph n).Dart}
    (hd : d ∈ p.darts) (he : e ∈ p.darts) (hde : d.snd = e.fst) :
    primalCompassQuarterTurn
      (parafermionicCoverCompassDirection d.fst.1 d.snd.1 d.adj)
      (parafermionicCoverCompassDirection e.fst.1 e.snd.1 e.adj) =
      parafermionicCoverPrimalCycleQuarterTurn p hp d.snd
        (Walk.dart_snd_mem_support_of_mem_darts p hd) := by
  let v := d.snd
  have hv : v ∈ p.support := Walk.dart_snd_mem_support_of_mem_darts p hd
  let q := p.rotate v hv
  have hqcycle : q.IsCycle := by
    simpa [q] using hp.rotate hv
  have hqnotnil : ¬ q.Nil := hqcycle.not_nil
  have hqfirstMem : q.firstDart hqnotnil ∈ p.darts := by
    apply (p.rotate_darts v hv).mem_iff.mp
    exact Walk.firstDart_mem_darts hqnotnil
  have hqlastMem : q.lastDart hqnotnil ∈ p.darts := by
    apply (p.rotate_darts v hv).mem_iff.mp
    exact Walk.lastDart_mem_darts hqnotnil
  have hlast : q.lastDart hqnotnil = d := by
    apply parafermionicCoverDart_snd_injective_of_isCycle p hp hqlastMem hd
    rfl
  have hfirst : q.firstDart hqnotnil = e := by
    apply parafermionicCoverDart_fst_injective_of_isCycle p hp hqfirstMem he
    change d.snd = e.fst
    exact hde
  have hin := parafermionicCoverPrimalCycleIncomingDirection_neighbor p hp v hv
  have hout := parafermionicCoverPrimalCycleOutgoingDirection_neighbor p hp v hv
  have hqpen : q.penultimate = d.toProd.1 := by
    have h := congrArg (fun z : (parafermionicCoverBoxGraph n).Dart => z.toProd.1) hlast
    simpa [Walk.lastDart] using h
  have hqnext : q.snd = e.toProd.2 := by
    have h := congrArg (fun z : (parafermionicCoverBoxGraph n).Dart => z.toProd.2) hfirst
    simpa [Walk.firstDart] using h
  have hsource : e.toProd.1 = v := by
    have h := congrArg (fun z : (parafermionicCoverBoxGraph n).Dart => z.toProd.1) hfirst
    simpa [Walk.firstDart, q, v] using h.symm
  have hinQ : parafermionicCoverCompassNeighbor q.penultimate.1
      (parafermionicCoverPrimalCycleIncomingDirection p hp v hv) = v.1 := by
    simpa [q, parafermionicCoverPrimalCycleRotate] using hin
  have hin' : parafermionicCoverCompassNeighbor d.fst.1
      (parafermionicCoverPrimalCycleIncomingDirection p hp v hv) = d.snd.1 := by
    rw [← hqpen]
    simpa [v] using hinQ
  have houtQ : parafermionicCoverCompassNeighbor v.1
      (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv) = q.snd.1 := by
    simpa [q, parafermionicCoverPrimalCycleRotate] using hout
  have hout' : parafermionicCoverCompassNeighbor e.fst.1
      (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv) = e.snd.1 := by
    simpa [v, hsource, hqnext] using houtQ
  have hdin := parafermionicCoverCompassDirection_eq_of_neighbor
    (show parafermionicCoverGraph.Adj d.fst.1 d.snd.1 from d.adj)
    (parafermionicCoverPrimalCycleIncomingDirection p hp v hv) hin'
  have hdout := parafermionicCoverCompassDirection_eq_of_neighbor
    (show parafermionicCoverGraph.Adj e.fst.1 e.snd.1 from e.adj)
    (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv) hout'
  simp [parafermionicCoverPrimalCycleQuarterTurn, v, hdin, hdout]

theorem parafermionicCoverWalkCompassDirections_map_induce
    {S : Set ParafermionicCoverVertex} {u v : S}
    (p : (parafermionicCoverGraph.induce S).Walk u v) :
    parafermionicCoverWalkCompassDirections
      (p.map (SimpleGraph.Embedding.induce S).toHom) =
    p.darts.map (fun d => parafermionicCoverCompassDirection
      d.fst.1 d.snd.1 d.adj) := by
  classical
  induction p with
  | nil => simp [parafermionicCoverWalkCompassDirections, Walk.map]
  | @cons a b c h q ih =>
      simp only [parafermionicCoverWalkCompassDirections_cons, Walk.map_cons,
        Walk.darts_cons, List.map_cons]
      rw [ih]
      rfl

private theorem parafermionicCoverPrimalCycle_cyclicCompassTurn_eq_tail_sum
    {n : ℕ} {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    parafermionicCoverWalkCyclicCompassTurn
      (p.map (SimpleGraph.Embedding.induce
        (parafermionicCoverBoxVertices n)).toHom) =
      (p.support.tail.map fun v =>
        if hv : v ∈ p.support then
          parafermionicCoverPrimalCycleQuarterTurn p hp v hv else 0).sum := by
  classical
  let dir : (parafermionicCoverBoxGraph n).Dart → Fin 4 := fun d =>
    parafermionicCoverCompassDirection d.fst.1 d.snd.1 (by exact d.adj)
  have hdir : parafermionicCoverWalkCompassDirections
      (p.map (SimpleGraph.Embedding.induce
        (parafermionicCoverBoxVertices n)).toHom) = p.darts.map dir := by
    simpa [dir, parafermionicCoverBoxGraph] using
      (parafermionicCoverWalkCompassDirections_map_induce
        (S := parafermionicCoverBoxVertices n) p)
  let f : ParafermionicCoverBoxVertex n → ℤ := fun v =>
    if hv : v ∈ p.support then parafermionicCoverPrimalCycleQuarterTurn p hp v hv else 0
  unfold parafermionicCoverWalkCyclicCompassTurn
  rw [hdir, ← List.map_rotate]
  rw [List.zipWith_map]
  rw [← List.map_uncurry_zip_eq_zipWith]
  have hrot : (p.darts.rotate 1).map (fun d => d.toProd.1) =
      p.darts.map (fun d => d.toProd.2) :=
    by
      rw [List.map_rotate]
      exact parafermionicCoverWalk_rotate_dart_fst_eq_snd p
  have hmapfst : (p.darts.zip (p.darts.rotate 1)).map
      Prod.fst = p.darts := by
    exact List.map_fst_zip (by simp)
  have hlist : (p.darts.zip (p.darts.rotate 1)).map
      (fun z => primalCompassQuarterTurn (dir z.1) (dir z.2)) =
      (p.darts.zip (p.darts.rotate 1)).map (fun z => f z.1.snd) := by
    apply List.map_congr_left
    intro z hz
    obtain ⟨d, e⟩ := z
    have hmem := List.of_mem_zip hz
    have hadj := parafermionicCover_mem_zip_endpoint_eq
      p.darts (p.darts.rotate 1) (fun d => d.toProd.1)
      (fun d => d.toProd.2) hrot hz
    have he : e ∈ p.darts := List.mem_rotate.mp hmem.2
    have hturn := parafermionicCoverPrimalCycle_pair_turn_eq_local
      p hp hmem.1 he hadj
    simpa [f, Walk.dart_snd_mem_support_of_mem_darts p hmem.1] using hturn
  have hzipmap : (p.darts.zip (p.darts.rotate 1)).map
      (fun z => f z.1.snd) = p.darts.map (fun d => f d.snd) := by
    calc
      (p.darts.zip (p.darts.rotate 1)).map (fun z => f z.1.snd) =
          ((p.darts.zip (p.darts.rotate 1)).map Prod.fst).map
            (fun d => f d.snd) := by simp [List.map_map]
      _ = p.darts.map (fun d => f d.snd) := by rw [hmapfst]
  have htail : p.darts.map (fun d => f d.snd) = p.support.tail.map f := by
    calc
      p.darts.map (fun d => f d.snd) =
          (p.darts.map (fun d => d.snd)).map f := by
        simp [List.map_map]
      _ = p.support.tail.map f := by rw [Walk.map_snd_darts]
  calc
    (List.map (fun z => primalCompassQuarterTurn (dir z.1) (dir z.2))
        (p.darts.zip (p.darts.rotate 1))).sum =
      ((p.darts.zip (p.darts.rotate 1)).map (fun z => f z.1.snd)).sum := by
        rw [hlist]
    _ = (p.darts.map (fun d => f d.snd)).sum := by
      rw [hzipmap]
    _ = (p.support.tail.map f).sum := by rw [htail]
    _ = (p.support.tail.map fun v =>
        if hv : v ∈ p.support then
          parafermionicCoverPrimalCycleQuarterTurn p hp v hv else 0).sum := by
      simp [f]

/-- For an actual finite-box simple cycle, the cyclic turn of its mapped full-cover
walk is exactly the already defined primal cycle turn sum. The zip includes the
last-to-first dart pair. -/
theorem parafermionicCoverWalkCyclicCompassTurn_map_boxCycle_eq_primalTurnSum
    {n : ℕ} {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    parafermionicCoverWalkCyclicCompassTurn
      (p.map (SimpleGraph.Embedding.induce
        (parafermionicCoverBoxVertices n)).toHom) =
      parafermionicCoverPrimalCycleTurnSum p hp := by
  classical
  let f : ParafermionicCoverBoxVertex n → ℤ := fun v =>
    if hv : v ∈ p.support then parafermionicCoverPrimalCycleQuarterTurn p hp v hv else 0
  calc
    parafermionicCoverWalkCyclicCompassTurn
        (p.map (SimpleGraph.Embedding.induce
          (parafermionicCoverBoxVertices n)).toHom) =
      (p.support.tail.map f).sum := by
        simpa [f] using parafermionicCoverPrimalCycle_cyclicCompassTurn_eq_tail_sum p hp
    _ = Finset.sum p.support.toFinset f :=
      (parafermionicCoverPrimalCycle_support_sum_eq_tail_map_sum p hp f).symm
    _ = parafermionicCoverPrimalCycleTurnSum p hp := by
      symm
      apply parafermionicCoverPrimalCycleTurnSum_eq_support_sum_of_local_eq p hp f
      intro v hv
      simp [f, hv]

/-- The discrete Umlaufsatz for every actual simple cycle in the full cover. -/
theorem parafermionicCoverWalkCyclicCompassTurn_eq_four_or_neg_four
    {u : ParafermionicCoverVertex} (p : parafermionicCoverGraph.Walk u u)
    (hp : p.IsCycle) :
    parafermionicCoverWalkCyclicCompassTurn p = 4 ∨
      parafermionicCoverWalkCyclicCompassTurn p = -4 := by
  obtain ⟨n, hn, hbox, hcycle, hmap⟩ :=
    parafermionicCoverCycle_exists_box_restriction p hp
  have hturn := parafermionicCoverPrimalCycleTurnSum_eq_four_or_neg_four hn _ hcycle
  rw [← parafermionicCoverWalkCyclicCompassTurn_map_boxCycle_eq_primalTurnSum _ hcycle,
    hmap] at hturn
  exact hturn

end PottsDiscontinuity.TorusTopology.Planar.Medial
