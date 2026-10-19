module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.DiagonalComparison
public import PottsDiscontinuity.RCMProof.XiLower

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open FK Duality CorrLength

def routeBRotatedBoundaryEvent (n : ℕ) : Set CorrLength.RotatedConfiguration :=
  ⋃ v : {v : CorrLength.RotatedVertex //
      max v.1.1.natAbs v.1.2.natAbs = n},
    CorrLength.rotatedConnectionEvent CorrLength.rotatedLatticeOrigin v.1

def routeBSquareBoundaryEvent (n : ℕ) : Set FK.LatticeConfiguration :=
  ⋃ v : {v : CorrLength.RotatedVertex //
      max v.1.1.natAbs v.1.2.natAbs = n},
    CorrLength.connectionEvent (0, 0) (CorrLength.rotatedVertexEquiv v.1)

def routeBSquareBoundaryTail (N : ℕ) : Set FK.LatticeConfiguration :=
  ⋃ k : {k : ℕ // N ≤ k}, routeBSquareBoundaryEvent k.1

private theorem routeBSquareBoundaryEvent_measurable (n : ℕ) :
    MeasurableSet (routeBSquareBoundaryEvent n) := by
  apply MeasurableSet.iUnion
  intro v
  exact CorrLength.connectionEvent_isMeasurableSet _ _

private theorem routeBSquareBoundaryTail_measurable (n : ℕ) :
    MeasurableSet (routeBSquareBoundaryTail n) := by
  apply MeasurableSet.iUnion
  intro k
  exact routeBSquareBoundaryEvent_measurable k.1

private theorem routeBSquareBoundaryTail_antitone :
    Antitone routeBSquareBoundaryTail := by
  intro m n hmn ω hω
  rcases Set.mem_iUnion.mp hω with ⟨k, hk⟩
  exact Set.mem_iUnion.mpr ⟨⟨k.1, hmn.trans k.2⟩, hk⟩

private theorem routeBSquareBoundaryTail_inter_finiteCluster_empty
    (ω : FK.LatticeConfiguration) (hfinite : (Duality.cluster ω (0, 0)).Finite) :
    ω ∉ ⋂ n, routeBSquareBoundaryTail n := by
  classical
  let S : Set ℕ := (fun x : ℤ × ℤ => max x.1.natAbs x.2.natAbs) ''
    Duality.cluster ω (0, 0)
  have hSfinite : S.Finite := hfinite.image _
  obtain ⟨K, hK⟩ := hSfinite.bddAbove
  intro hω
  have htail := Set.mem_iInter.mp hω (2 * K + 1)
  rcases Set.mem_iUnion.mp htail with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨v, hv⟩
  let x := CorrLength.rotatedVertexEquiv v.1
  have hxconn : x ∈ Duality.cluster ω (0, 0) :=
    (CorrLength.connectionEvent_iff_rcInfiniteReachable (0, 0) x ω).1 hv
  have hcoords := congrArg Subtype.val
      (CorrLength.squareToRotated_rotatedToSquare v.1)
  have hfirst : v.1.1.1 = x.1 - x.2 := by
    have h := congrArg Prod.fst hcoords
    simpa [x, CorrLength.rotatedVertexEquiv, CorrLength.rotatedToSquareVertex,
      CorrLength.squareToRotatedVertex] using h.symm
  have hsecond : v.1.1.2 = x.1 + x.2 := by
    have h := congrArg Prod.snd hcoords
    simpa [x, CorrLength.rotatedVertexEquiv, CorrLength.rotatedToSquareVertex,
      CorrLength.squareToRotatedVertex] using h.symm
  have hfirstBound : v.1.1.1.natAbs ≤ x.1.natAbs + x.2.natAbs := by
    have hcast : (v.1.1.1.natAbs : ℤ) ≤
        ((x.1.natAbs + x.2.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_add,
        Int.natCast_natAbs, Int.natCast_natAbs, hfirst]
      simpa using abs_sub_le x.1 0 x.2
    exact_mod_cast hcast
  have hsecondBound : v.1.1.2.natAbs ≤ x.1.natAbs + x.2.natAbs := by
    have hcast : (v.1.1.2.natAbs : ℤ) ≤
        ((x.1.natAbs + x.2.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_add,
        Int.natCast_natAbs, Int.natCast_natAbs, hsecond]
      simpa using abs_sub_le x.1 0 (-x.2)
    exact_mod_cast hcast
  have hshell : max v.1.1.1.natAbs v.1.1.2.natAbs = k.1 := by
    exact v.2
  have hknorm : k.1 ≤ x.1.natAbs + x.2.natAbs := by
    rw [← hshell]
    exact max_le hfirstBound hsecondBound
  have hxK : max x.1.natAbs x.2.natAbs ≤ K := by
    apply hK
    exact ⟨x, hxconn, rfl⟩
  have hkK : k.1 ≤ 2 * K := by omega
  omega

/-- A free rotated boundary connection tends to zero when the square-lattice
free origin cluster is almost surely finite. The proof uses continuity from
above on the union of all shell events beyond a given radius. -/
theorem rotatedBoundaryConnectionProbability_tendsto_zero_of_ae_finite_cluster
    (θ : FK.Parameters) (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (hfinite : ∀ᵐ ω ∂μ, (Duality.cluster ω (0, 0)).Finite) :
    Filter.Tendsto (fun n : ℕ =>
      (CorrLength.rotatedFreeBoxLimit θ).toMeasure.real
        (routeBRotatedBoundaryEvent n)) Filter.atTop (nhds 0) := by
  have := hμ.1
  let ν : ProbabilityMeasure FK.LatticeConfiguration :=
    Classical.choose (FK.freeBoxLimit_existsUnique θ)
  have hweak : Filter.Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n)
      Filter.atTop (nhds ν) :=
    (Classical.choose_spec (FK.freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      FK.origin_latticeBox_nested FK.origin_latticeBox_exhaustive
  have hν : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 ν.toMeasure :=
    FK.isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hweak
  have hμν : μ = ν.toMeasure :=
    PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ hν
  let H := CorrLength.rotatedConfigurationHomeomorph
  have hrotMeas (n : ℕ) : MeasurableSet (routeBRotatedBoundaryEvent n) := by
    apply MeasurableSet.iUnion
    intro v
    exact CorrLength.rotatedConnectionEvent_isMeasurableSet _ _
  have hpre (n : ℕ) : H.toFun ⁻¹' routeBRotatedBoundaryEvent n =
      routeBSquareBoundaryEvent n := by
    ext ω
    simp [routeBRotatedBoundaryEvent, routeBSquareBoundaryEvent, H,
      CorrLength.rotatedConnectionEvent, CorrLength.rotatedLatticeOrigin,
      CorrLength.rotatedVertexEquiv, CorrLength.rotatedToSquareVertex]
  have hprob (n : ℕ) :
      (CorrLength.rotatedFreeBoxLimit θ).toMeasure.real
          (routeBRotatedBoundaryEvent n) =
        μ.real (routeBSquareBoundaryEvent n) := by
    have hmap := ProbabilityMeasure.map_apply ν
      H.continuous_toFun.measurable.aemeasurable (hrotMeas n)
    rw [hpre n] at hmap
    calc
      (CorrLength.rotatedFreeBoxLimit θ).toMeasure.real
          (routeBRotatedBoundaryEvent n) =
        ((CorrLength.rotatedFreeBoxLimit θ)
          (routeBRotatedBoundaryEvent n) : NNReal) :=
        ProbabilityMeasure.measureReal_eq_coe_coeFn _ _
      _ = (ν (routeBSquareBoundaryEvent n) : NNReal) := by
        simpa [CorrLength.rotatedFreeBoxLimit, H, ν] using hmap
      _ = μ.real (routeBSquareBoundaryEvent n) := by
        rw [hμν, ProbabilityMeasure.measureReal_eq_coe_coeFn]
  have hnull : μ (⋂ n, routeBSquareBoundaryTail n) = 0 := by
    have hsubset : (⋂ n, routeBSquareBoundaryTail n) ⊆
        {ω | ¬ (Duality.cluster ω (0, 0)).Finite} := by
      intro ω hω hfiniteω
      exact routeBSquareBoundaryTail_inter_finiteCluster_empty ω hfiniteω hω
    have hfiniteNull : μ {ω | ¬ (Duality.cluster ω (0, 0)).Finite} = 0 := by
      rw [← MeasureTheory.ae_iff]
      exact hfinite
    exact measure_mono_null hsubset hfiniteNull
  have hcontinuous := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := μ) (s := routeBSquareBoundaryTail)
    (fun n => (routeBSquareBoundaryTail_measurable n).nullMeasurableSet)
    routeBSquareBoundaryTail_antitone
    ⟨0, measure_ne_top μ _⟩
  have htailENN : Filter.Tendsto (fun n => μ (routeBSquareBoundaryTail n))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def, hnull] using hcontinuous
  have htailReal : Filter.Tendsto
      (fun n => (μ (routeBSquareBoundaryTail n)).toReal)
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp htailENN
    change Filter.Tendsto
      (ENNReal.toReal ∘ (fun n => μ (routeBSquareBoundaryTail n)))
      Filter.atTop (nhds (ENNReal.toReal 0))
    exact h
  have hprobSmall : Filter.Tendsto
      (fun n => μ.real (routeBSquareBoundaryEvent n))
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    · exact tendsto_const_nhds
    · exact htailReal
    · intro n
      exact measureReal_nonneg
    · intro n
      have hsub : routeBSquareBoundaryEvent n ⊆ routeBSquareBoundaryTail n := by
        intro ω hω
        exact Set.mem_iUnion.mpr ⟨⟨n, le_rfl⟩, hω⟩
      exact measureReal_mono hsub
  have hseq : (fun n =>
      (CorrLength.rotatedFreeBoxLimit θ).toMeasure.real
        (routeBRotatedBoundaryEvent n)) =
      (fun n => μ.real (routeBSquareBoundaryEvent n)) := by
    funext n
    exact hprob n
  rw [hseq]
  exact hprobSmall

/-- Absence of percolation for the critical free measure, derived from the positive lower
bound on the inverse correlation length, as the input of Lemma 3.14: (3.24) and Identity (4.4)
give a positive rate;
the resulting exponential decay makes the free origin cluster finite a.s.,
and the rotated boundary connection probability tends to zero. -/
theorem routeB_free_nonpercolation_and_boundary_decay
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW21 : contract_eq315)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) /
        (n : ℝ)) Filter.atTop (nhds ξinv)) :
    ∃ S : ℝ,
      Filter.Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2)))
        Filter.atTop (nhds S) ∧
      ξinv ≥ Real.arcosh (Real.sqrt q.val / 2) + 2 * S ∧
      μ (Duality.infiniteClusterAt (0, 0)) = 0 ∧
      Filter.Tendsto (fun n : ℕ =>
        (CorrLength.rotatedFreeBoxLimit (FK.criticalParameters q)).toMeasure.real
          (routeBRotatedBoundaryEvent n)) Filter.atTop (nhds 0) := by
  have := hμ.1
  obtain ⟨S, hS, hxi⟩ := xi_inverse_ge_critical_rate
    hW12i hW12ii hW21 q hh319 hq μ hμ ξinv hRate
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  have hlam : 0 < lam := by
    dsimp [lam]
    apply Real.arcosh_pos
    have hqpos : 0 < q.val := by linarith
    have hsquare := Real.sq_sqrt (le_of_lt hqpos)
    have hsqrt : 2 < Real.sqrt q.val := by
      nlinarith [Real.sqrt_nonneg q.val, hq]
    linarith
  obtain ⟨S₀, T, hS₀, hT, hpositive, hidentity⟩ :=
    PottsDiscontinuity.identity44 lam hlam
  have hS_eq : S = S₀ := tendsto_nhds_unique hS hS₀
  have hRpositive : 0 < lam + 2 * S := by
    rw [hS_eq]
    exact hpositive
  have hxiPositive : 0 < ξinv := by
    have hxi' : lam + 2 * S ≤ ξinv := by simpa [lam] using hxi
    exact lt_of_lt_of_le hRpositive hxi'
  have hRateDual : Filter.Tendsto (fun n : ℕ =>
      -(1 / (n : ℝ)) * Real.log
        (Duality.twoPoint μ (diagonalSite n))) Filter.atTop (nhds ξinv) := by
    refine hRate.congr' ?_
    filter_upwards with n
    have hevent : CorrLength.connectionEvent (0, 0) (diagonalSite n) =
        Duality.connectionEvent (0, 0) (diagonalSite n) := by
      ext ω
      rw [CorrLength.connectionEvent_iff_rcInfiniteReachable]
      rfl
    rw [hevent]
    simp only [Duality.twoPoint]
    rw [show Duality.connectionEvent (0, 0) (diagonalSite n) =
      Duality.connectionEvent 0 (diagonalSite n) by rfl]
    rw [div_eq_mul_inv]
    ring
  obtain ⟨C, c, hC, hc, hdecay⟩ :=
    Duality.free_exponential_decay_of_pos_diagonal_rate
      (FK.criticalParameters q) μ hμ ξinv hxiPositive hRateDual
  have hclusterBound : ∀ x : ℤ × ℤ,
      μ (Duality.connectionEvent (0, 0) x) ≤ ENNReal.ofReal
        (C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) := by
    intro x
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    apply ENNReal.ofReal_le_ofReal
    change μ.real (Duality.connectionEvent 0 x) ≤ _
    exact hdecay x
  have hfinite : ∀ᵐ ω ∂μ, (Duality.cluster ω (0, 0)).Finite :=
    Duality.ae_finite_cluster_of_exponential_decay μ (0, 0) C c hc hclusterBound
  have hno : μ (Duality.infiniteClusterAt (0, 0)) = 0 :=
    Duality.infiniteClusterAt_zero_of_exponential_decay μ C c hc hclusterBound
  have hboundary := rotatedBoundaryConnectionProbability_tendsto_zero_of_ae_finite_cluster
    (FK.criticalParameters q) μ hμ hfinite
  exact ⟨S, hS, hxi, hno, hboundary⟩

end PottsDiscontinuity.RCMProof
