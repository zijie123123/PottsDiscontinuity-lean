module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.TorusLoops.Lemma314Corrected

@[expose] public section

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open MeasureTheory

/-- The corrected Lemma 3.14 (`TorusLoops.lemma_3_14_corrected_limsup`) is consumed with its
actual square-box
boundary-decay premise and its limsup-in-height conclusion. -/
theorem corrected_lemma314_proved : corrected_lemma314 := by
  intro q hzero
  exact TorusLoops.lemma_3_14_corrected_limsup q hzero

/-- The square-box premise required by the corrected Lemma 3.14 follows from the nonpercolation
conclusion in Route B. The rectangle and critical parameter records are the
same record, and the free-box limit is unique. -/
theorem lemma314_square_boundary_decay_of_nonpercolation
    (q : Set.Ici (1 : ℝ)) (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (hno : μ (Duality.infiniteClusterAt (0, 0)) = 0) :
    Filter.Tendsto
      (fun n => (((Classical.choose (FK.freeBoxLimit_existsUnique
        (TorusLoops.rectangleFKParameters q)))
          (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ))
      Filter.atTop (nhds 0) := by
  let θ : FK.Parameters := TorusLoops.rectangleFKParameters q
  have hθ : θ = FK.criticalParameters q := rfl
  let ν : MeasureTheory.ProbabilityMeasure FK.LatticeConfiguration :=
    Classical.choose (FK.freeBoxLimit_existsUnique θ)
  have hweak : Filter.Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n)
      Filter.atTop (nhds ν) :=
    (Classical.choose_spec (FK.freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      FK.origin_latticeBox_nested FK.origin_latticeBox_exhaustive
  have hν : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 ν.toMeasure :=
    FK.isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hweak
  have hμ' : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ := by
    simpa only [hθ] using hμ
  have hμν : μ = ν.toMeasure :=
    PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ' hν
  have hnoν : ν.toMeasure (RCInfinite.infiniteAt (0, 0)) = 0 := by
    rw [← hμν]
    simpa [Duality.infiniteClusterAt, Duality.cluster,
      RCInfinite.infiniteAt, RCInfinite.cluster] using hno
  have hzeroENN : Filter.Tendsto
      (fun n => ν.toMeasure (Zhang.boundaryConnectionEvent n))
      Filter.atTop (nhds 0) :=
    (Zhang.tendsto_boundaryConnection_zero_iff ν.toMeasure).2 hnoν
  have hzeroReal : Filter.Tendsto
      (fun n => (ν.toMeasure (Zhang.boundaryConnectionEvent n)).toReal)
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hzeroENN
    simpa [Function.comp_def] using h
  have hseq : (fun n =>
      (((ν (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ))) =
      (fun n => (ν.toMeasure (Zhang.boundaryConnectionEvent n)).toReal) := by
    funext n
    symm
    change ν.toMeasure.real (Zhang.boundaryConnectionEvent n) = _
    exact ProbabilityMeasure.measureReal_eq_coe_coeFn ν
      (Zhang.boundaryConnectionEvent n)
  change Filter.Tendsto
    (fun n => (((ν (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ)))
    Filter.atTop (nhds 0)
  simpa only [hseq] using hzeroReal

/-- For a fixed even width, the normalized loop-observable log rate is
eventually bounded above once the one-arm input of the corrected Lemma 3.14 holds. This
supplies the ordinary real-sequence boundedness needed to read its limsup conclusion. -/
theorem windingLoopDensityLogRate_abs_bounded
    (q : Set.Ici (1 : ℝ)) {N : ℕ} (hN : Even N) (hNp : 0 < N)
    (harm : TorusLoops.rectangleFreeOneArmProbability q (N / 2 - 1) ≤
      TorusLoops.windingLoopTailArmThreshold q 1) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => abs (TorusLoops.windingLoopDensityLogRate hN hNp q n)) := by
  let τ := TorusLoops.windingLoopTailArmThreshold q 1
  let C₀ := TorusLoops.windingLoopDensityLogOffset q
  let C₁ := TorusLoops.windingLoopDensityLogSlope q
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; exact TorusLoops.windingLoopDensityLogOffset_nonneg q
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; exact TorusLoops.windingLoopDensityLogSlope_nonneg q
  have hC : 0 ≤ C₀ + C₁ := add_nonneg hC₀ hC₁
  let K := C₁ / 2 + (C₀ + C₁) / 2
  have hbounded : ∀ᶠ n : ℕ in Filter.atTop,
      abs (TorusLoops.windingLoopDensityLogRate hN hNp q n) ≤ K := by
    filter_upwards [Filter.eventually_ge_atTop (9 * N)] with n hn
    have hNle : N ≤ 2 * (n + 1) := by omega
    have hthreshold : 9 * N ≤ (n + 1) / 1 + 1 := by omega
    have hrate := TorusLoops.abs_windingLoopDensityLogRate_le
      hN hNp q 1 n (by norm_num) hNle hthreshold (by simpa [τ] using harm)
    have hrate' :
        abs (TorusLoops.windingLoopDensityLogRate hN hNp q n) ≤
          C₁ / (2 * (1 : ℝ)) + (C₀ + C₁) / (2 * ((n + 1 : ℕ) : ℝ)) := by
      simpa [C₀, C₁] using hrate
    have hfirst : C₁ / (2 * (1 : ℝ)) = C₁ / 2 := by norm_num
    rw [hfirst] at hrate'
    have hden : 2 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 n)
      nlinarith
    have hrem : (C₀ + C₁) / (2 * ((n + 1 : ℕ) : ℝ)) ≤ (C₀ + C₁) / 2 :=
      div_le_div_of_nonneg_left hC (by norm_num) hden
    calc
      abs (TorusLoops.windingLoopDensityLogRate hN hNp q n) ≤
          C₁ / 2 + (C₀ + C₁) / (2 * ((n + 1 : ℕ) : ℝ)) := hrate'
      _ ≤ C₁ / 2 + (C₀ + C₁) / 2 := add_le_add le_rfl hrem
      _ = K := rfl
  exact Filter.isBoundedUnder_of_eventually_le hbounded

/-- A single width cutoff combines the limsup estimate of the corrected Lemma 3.14 with the one-arm
threshold needed to know the rate sequence is ordinarily bounded. -/
theorem lemma314_limsup_and_one_arm_cutoff
    (q : Set.Ici (1 : ℝ))
    (hzero : Filter.Tendsto
      (fun n => (((Classical.choose (FK.freeBoxLimit_existsUnique
        (TorusLoops.rectangleFKParameters q)))
          (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ))
      Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : {k : ℕ // 2 ≤ k}, ∀ (N : ℕ) (hN : Even N)
      (hNlarge : N₀.val ≤ N),
      Filter.limsup
        (fun n => abs (TorusLoops.windingLoopDensityLogRate hN (by omega) q n))
        Filter.atTop ≤ ε ∧
      TorusLoops.rectangleFreeOneArmProbability q (N / 2 - 1) ≤
        TorusLoops.windingLoopTailArmThreshold q 1 := by
  obtain ⟨Nlim, hlim⟩ := corrected_lemma314_proved q hzero ε hε
  have hdecay := TorusLoops.tendsto_rectangleFreeOneArmProbability_of_boundaryConnection_zero q hzero
  have hτ : 0 < TorusLoops.windingLoopTailArmThreshold q 1 :=
    TorusLoops.windingLoopTailArmThreshold_pos q 1
  have harmEventually : ∀ᶠ N : ℕ in Filter.atTop,
      TorusLoops.rectangleFreeOneArmProbability q (N / 2 - 1) ≤
        TorusLoops.windingLoopTailArmThreshold q 1 := by
    filter_upwards [hdecay.eventually (Iio_mem_nhds hτ)] with N hN
    exact hN.le
  obtain ⟨Narm, harm⟩ := Filter.eventually_atTop.1 harmEventually
  refine ⟨⟨max Nlim.val Narm, ?_⟩, ?_⟩
  · exact le_trans Nlim.property (le_max_left Nlim.val Narm)
  intro N hN hNlarge
  have hnlim : Nlim.val ≤ N := (le_max_left Nlim.val Narm).trans hNlarge
  have hnarm : Narm ≤ N := (le_max_right Nlim.val Narm).trans hNlarge
  have hlim' := hlim N hN hnlim
  have harm' := harm N hnarm
  exact ⟨hlim', harm'⟩

end PottsDiscontinuity.RCMProof
