module

public import PottsDiscontinuity.CorrLength.ConnectionEvents
public import PottsDiscontinuity.FK.Events

/-!
# Positive probability of finite-distance connection

Every pair of square-lattice vertices has a deterministic finite path. The
event that all of its edges are open has positive probability in a sufficiently
large finite free box, and hence in the canonical free limit.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.CorrLength

open PottsDiscontinuity.FK

noncomputable section

private theorem squareLattice_reachable_origin_posX (n : ℕ) :
    squareLattice.Reachable (0, 0) ((n : ℤ), 0) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hadj : squareLattice.Adj ((n : ℤ), 0) (((n + 1 : ℕ) : ℤ), 0) := by
        rw [squareLattice_adj_iff]
        left
        exact ⟨Or.inl (by simp), rfl⟩
      exact ih.trans hadj.reachable

private theorem squareLattice_reachable_origin_negX (n : ℕ) :
    squareLattice.Reachable (0, 0) (-((n : ℤ)), 0) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hadj : squareLattice.Adj (-(n : ℤ), 0) (-((n + 1 : ℕ) : ℤ), 0) := by
        rw [squareLattice_adj_iff]
        left
        exact ⟨Or.inr (by omega), rfl⟩
      exact ih.trans hadj.reachable

private theorem squareLattice_reachable_origin_posY (n : ℕ) :
    squareLattice.Reachable (0, 0) (0, (n : ℤ)) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hadj : squareLattice.Adj (0, (n : ℤ)) (0, ((n + 1 : ℕ) : ℤ)) := by
        rw [squareLattice_adj_iff]
        right
        exact ⟨rfl, Or.inl (by simp)⟩
      exact ih.trans hadj.reachable

private theorem squareLattice_reachable_origin_negY (n : ℕ) :
    squareLattice.Reachable (0, 0) (0, -((n : ℤ))) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hadj : squareLattice.Adj (0, -(n : ℤ)) (0, -((n + 1 : ℕ) : ℤ)) := by
        rw [squareLattice_adj_iff]
        right
        exact ⟨rfl, Or.inr (by omega)⟩
      exact ih.trans hadj.reachable

private theorem squareLattice_reachable_origin_x (a : ℤ) :
    squareLattice.Reachable (0, 0) (a, 0) := by
  cases a with
  | ofNat n => simpa using squareLattice_reachable_origin_posX n
  | negSucc n =>
      rw [Int.negSucc_eq]
      convert squareLattice_reachable_origin_negX (n + 1) using 1
      push_cast; ring

private theorem squareLattice_reachable_origin_y (b : ℤ) :
    squareLattice.Reachable (0, 0) (0, b) := by
  cases b with
  | ofNat n => simpa using squareLattice_reachable_origin_posY n
  | negSucc n =>
      rw [Int.negSucc_eq]
      convert squareLattice_reachable_origin_negY (n + 1) using 1
      push_cast; ring

private theorem squareLattice_reachable_all (u v : LatticeVertex) :
    squareLattice.Reachable u v := by
  let d : LatticeVertex := (v.1 - u.1, v.2 - u.2)
  have hx := squareLattice_reachable_origin_x d.1
  have hy := squareLattice_reachable_origin_y d.2
  have hy' : squareLattice.Reachable (d.1, 0) (d.1, d.2) := by
    have h := (SimpleGraph.Iso.reachable_iff
      (φ := latticeTranslationIso (d.1, 0)) (u := (0, 0)) (v := (0, d.2))).mpr hy
    simpa [d, latticeTranslationIso, latticeTranslate] using h
  have h := hx.trans hy'
  have h' : squareLattice.Reachable (latticeTranslate u (0, 0))
      (latticeTranslate u d) := by
    exact (SimpleGraph.Iso.reachable_iff
      (φ := latticeTranslationIso u) (u := (0, 0)) (v := d)).mpr h
  simpa [d, latticeTranslate] using h'

private theorem squareLattice_reachable_finite_actualConnected {u v : LatticeVertex}
    (h : squareLattice.Reachable u v) :
    ∃ F : Finset squareLattice.edgeSet, ActualConnected squareLattice F u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact ⟨∅, by simp⟩
  | @cons u v w huv tail ih =>
      obtain ⟨F, hF⟩ := ih
      let e : squareLattice.edgeSet := ⟨s(u, v), squareLattice.mem_edgeSet.mpr huv⟩
      refine ⟨insert e F, ?_⟩
      have hfirst : ActualConnected squareLattice (insert e F) u v := by
        have hAdj : (openGraph squareLattice (insert e F)).Adj u v := by
          apply (openGraph_adj squareLattice (insert e F) u v).mpr
          change s(u, v) ∈ Subtype.val '' (↑(insert e F) : Set squareLattice.edgeSet)
          exact ⟨e, by simp [e], rfl⟩
        exact hAdj.reachable
      exact hfirst.trans (actualConnected_mono (Finset.subset_insert e F) hF)

private theorem exists_finite_connection_witness (u v : LatticeVertex) :
    ∃ F : Finset squareLattice.edgeSet, ActualConnected squareLattice F u v :=
  squareLattice_reachable_finite_actualConnected (squareLattice_reachable_all u v)

private theorem eventually_edge_lift_origin_boxGraph (e : squareLattice.edgeSet) :
    ∀ᶠ n : ℕ in atTop, ∃ f : (boxGraph (0, 0) n).edgeSet,
      Sym2.map Subtype.val f.1 = e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      filter_upwards [eventually_mem_box x, eventually_mem_box y] with n hx hy
      have hx' : x ∈ latticeBox (0, 0) n := by
        rw [latticeBox_origin_eq_box]
        exact hx
      have hy' : y ∈ latticeBox (0, 0) n := by
        rw [latticeBox_origin_eq_box]
        exact hy
      let u : BoxVertex (0, 0) n := ⟨x, hx'⟩
      let v : BoxVertex (0, 0) n := ⟨y, hy'⟩
      have hAdj : squareLattice.Adj x y := squareLattice.mem_edgeSet.mp he
      have hboxAdj : (boxGraph (0, 0) n).Adj u v := by
        rw [boxGraph_adj_iff]
        exact hAdj
      have hboxEdge : s(u, v) ∈ (boxGraph (0, 0) n).edgeSet :=
        (boxGraph (0, 0) n).mem_edgeSet.mpr hboxAdj
      refine ⟨⟨s(u, v), hboxEdge⟩, ?_⟩
      simp [u, v]

private theorem freeBoxLimit_allOpen_pos (θ : Parameters)
    (F : Finset squareLattice.edgeSet) :
    Classical.choose (freeBoxLimit_existsUnique θ) (LatticeConfiguration.allOpen F) > 0 := by
  classical
  have hLift : ∀ᶠ n : ℕ in atTop, ∀ e ∈ F,
      ∃ f : (boxGraph (0, 0) n).edgeSet,
        Sym2.map Subtype.val f.1 = e.1 :=
    (eventually_all_finset F).2 fun e _ => eventually_edge_lift_origin_boxGraph e
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hLift
  have hnonempty :
      {A : Configuration (boxGraph (0, 0) N) |
        F ⊆ A.map (boxEdgeEmbedding (0, 0) N)}.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    intro e he
    let ex := hN N le_rfl e he
    let f : (boxGraph (0, 0) N).edgeSet := Classical.choose ex
    have hfe := Classical.choose_spec ex
    apply Finset.mem_map.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    change Sym2.map Subtype.val f.1 = e.1
    exact hfe
  have hbox : 0 < ((boxProbabilityMeasure θ (0, 0) N : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F)) := by
    rw [boxProbabilityMeasure_allOpen]
    exact (measure_pos_iff (boxGraph (0, 0) N) θ (BoundaryCondition.free ∅) _).2 hnonempty
  have hboxNN : 0 < boxProbabilityMeasure θ (0, 0) N
      (LatticeConfiguration.allOpen F) := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hbox
    exact ENNReal.coe_pos.mp hbox
  let ν : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (freeBoxLimit_existsUnique θ)
  have hweak : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 ν) :=
    (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
  have hconv := LatticeConfiguration.tendsto_allOpen_of_weak hweak F
  have hmono (n : ℕ) (hn : N ≤ n) :
      boxProbabilityMeasure θ (0, 0) N (LatticeConfiguration.allOpen F) ≤
        boxProbabilityMeasure θ (0, 0) n (LatticeConfiguration.allOpen F) := by
    have h := boxProbabilityMeasure_allOpen_mono θ (0, 0) (0, 0) N n
      (latticeBox_mono (0, 0) hn) F
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
    exact ENNReal.coe_le_coe.mp h
  have hlimit : boxProbabilityMeasure θ (0, 0) N
      (LatticeConfiguration.allOpen F) ≤ ν (LatticeConfiguration.allOpen F) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hconv
      (Filter.eventually_atTop.2 ⟨N, fun n hn => hmono n hn⟩)
  exact lt_of_lt_of_le hboxNN hlimit

/-- Every fixed finite-distance connection has strictly positive probability
under the canonical free box limit. -/
theorem freeBoxLimit_connection_positive (θ : Parameters) (u v : LatticeVertex) :
    ((Classical.choose (freeBoxLimit_existsUnique θ) : ProbabilityMeasure
      LatticeConfiguration).toMeasure).real (connectionEvent u v) > 0 := by
  obtain ⟨F, hF⟩ := exists_finite_connection_witness u v
  have hsubset : LatticeConfiguration.allOpen F ⊆ connectionEvent u v := by
    intro ω hω
    exact ⟨F, hF, hω⟩
  let ν : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (freeBoxLimit_existsUnique θ)
  have hbox := freeBoxLimit_allOpen_pos θ F
  have hmono : ν.toMeasure (LatticeConfiguration.allOpen F) ≤
      ν.toMeasure (connectionEvent u v) :=
    measure_mono (μ := ν.toMeasure) hsubset
  have hpos : 0 < ν.toMeasure (connectionEvent u v) := by
    have hleft : 0 < ν.toMeasure (LatticeConfiguration.allOpen F) := by
      rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact ENNReal.coe_pos.mpr (by simpa only [Prod.forall, gt_iff_lt, ν] using hbox)
    exact lt_of_lt_of_le hleft hmono
  simpa only [Prod.forall, Measure.real_def, gt_iff_lt, ν] using
    ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _)

/-- Every free infinite-volume limit has strictly positive probability of a
finite-distance connection. -/
theorem isRCInfiniteVolumeLimit_connection_positive (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (u v : LatticeVertex) :
    μ.real (connectionEvent u v) > 0 := by
  let ν : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (freeBoxLimit_existsUnique θ)
  have hweak : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 ν) :=
    (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
  have hν : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 ν.toMeasure :=
    isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hweak
  have hEq : μ = ν.toMeasure :=
    PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ hν
  rw [hEq]
  exact freeBoxLimit_connection_positive θ u v

end

end PottsDiscontinuity.CorrLength
