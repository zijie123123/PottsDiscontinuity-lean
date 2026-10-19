module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Infra.Lambda
public import PottsDiscontinuity.PottsThm.ColoringPushforward
public import PottsDiscontinuity.PottsThm.CriticalLimits
public import PottsDiscontinuity.PottsThm.Distinctness
public import PottsDiscontinuity.PottsThm.MixtureSeparation
public import PottsDiscontinuity.PottsThm.PottsColoringErgodicity
public import PottsDiscontinuity.PottsThm.RateTransfer

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.Duality
open PottsDiscontinuity.RCInfinite

private theorem probabilityMeasure_eq_of_spinCylinder_real (q : ℕ) (hq : 2 ≤ q)
    (μ ν : ProbabilityMeasure (SpinSpace q))
    (h : ∀ A ξ, μ.toMeasure.real (spinCylinder q A ξ) =
      ν.toMeasure.real (spinCylinder q A ξ)) : μ = ν := by
  apply spinCylinderCoordinates_injective q hq
  funext i
  apply NNReal.coe_injective
  simpa only [spinCylinderCoordinates,
    ProbabilityMeasure.measureReal_eq_coe_coeFn] using h i.1 i.2

/-- Theorem 1.1 follows from the stated random-cluster rate input at every
positive solution of `cosh λ = √q / 2`. -/
theorem potts_theorem_1_1_of_rc_rate (q : ℕ) (hq : 4 < q)
    (hRCrate : ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∀ φ₀ : Measure LatticeConfiguration,
        IsRCInfiniteVolumeLimit
          (rcCriticalParameter ⟨(q : ℝ), by
            change (1 : ℝ) ≤ (q : ℝ)
            exact_mod_cast (show 1 ≤ q by omega)⟩)
          ⟨(q : ℝ), by
            change (0 : ℝ) < (q : ℝ)
            exact_mod_cast (show 0 < q by omega)⟩ 0 φ₀ →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
            (φ₀.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S)) ∧ 0 < lam + 2 * S) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real
        {σ | ((σ (0, 0) : ℕ)) = (i.succ : ℕ)}) ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S) := by
  classical
  have hq2 : 2 ≤ q := by omega
  have hqReal : (4 : ℝ) < q := by exact_mod_cast hq
  have hβ : 0 < pottsCriticalBeta q := pottsCriticalBeta_pos q hq
  let qI : Set.Ici (1 : ℝ) := ⟨(q : ℝ), by
    change (1 : ℝ) ≤ (q : ℝ)
    exact_mod_cast (show 1 ≤ q by omega)⟩
  let qO : Set.Ioi (0 : ℝ) := ⟨(q : ℝ), by
    change (0 : ℝ) < (q : ℝ)
    exact_mod_cast (show 0 < q by omega)⟩
  have : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have hcriticalParams :
      (criticalFKParameters q hq).toP = rcCriticalParameter qI ∧
        (criticalFKParameters q hq).toQ = qO := by
    have hbridge := fkCritical_toP_toQ q hq
    constructor
    · rw [hbridge.1]
      rfl
    · rw [hbridge.2]
      apply Subtype.ext
      rfl
  obtain ⟨μP, φ₀, φp, hRC₀, hμ₀, hES₀, hrest⟩ :=
    exists_critical_coloured_limits q hq
  have hRCp : ∀ k : Fin q,
      IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
        (criticalFKParameters q hq).toQ 1 (φp k).toMeasure :=
    fun k => (hrest k).1
  have hμp : ∀ k : Fin q,
      IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) k.succ
        (μP k.succ).toMeasure := fun k => (hrest k).2.1
  have hESp : ∀ k : Fin q,
      IsWiredEdwardsSokalColouring q (φp k).toMeasure k.succ
        (by simp only [Fin.val_succ]; omega) (μP k.succ).toMeasure :=
    fun k => (hrest k).2.2
  have hRC₀external : IsRCInfiniteVolumeLimit (rcCriticalParameter qI) qO 0
      φ₀.toMeasure := by
    rw [← hcriticalParams.1, ← hcriticalParams.2]
    exact hRC₀
  let lam₀ : ℝ := Real.arcosh (Real.sqrt q / 2)
  have hlam₀ : 0 < lam₀ := by
    dsimp [lam₀]
    exact (arcosh_pos_of_gt4 (q : ℝ) hqReal).1
  have hcosh₀ : Real.cosh lam₀ = Real.sqrt q / 2 := by
    dsimp [lam₀]
    exact (arcosh_pos_of_gt4 (q : ℝ) hqReal).2
  obtain ⟨S₀, hseries₀, hrate₀, hpositive₀⟩ :=
    hRCrate lam₀ hlam₀ hcosh₀ φ₀.toMeasure hRC₀external
  let k₀ : Fin q := ⟨0, by omega⟩
  have hdisc (k : Fin q) := rc_discontinuity_of_positive_rate q hq φ₀ (φp k)
    hRC₀ (hRCp k) (lam₀ + 2 * S₀) hpositive₀ hrate₀
  have hno : φ₀.toMeasure Duality.existsInfiniteCluster = 0 :=
    free_no_infinite_clusters (criticalFKParameters q hq) φ₀.toMeasure hRC₀ (hdisc k₀).1
  have hφ₀weak : Tendsto
      (fun n => boxProbabilityMeasure
        (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0) n)
      atTop (𝓝 φ₀) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 0 φ₀.toMeasure hRC₀
    have htarget :
        (⟨φ₀.toMeasure, hRC₀.1⟩ : ProbabilityMeasure LatticeConfiguration) = φ₀ := by
      ext
      rfl
    rw [htarget] at ht
    simpa [boxMeasure_free, criticalFKParameters, fkParameters] using ht
  have hφpweak (k : Fin q) : Tendsto
      (fun n => wiredBoxProbabilityMeasure
        (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0) n)
      atTop (𝓝 (φp k)) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 1
      (φp k).toMeasure (hRCp k)
    have htarget :
        (⟨(φp k).toMeasure, (hRCp k).1⟩ : ProbabilityMeasure LatticeConfiguration) = φp k := by
      ext
      rfl
    rw [htarget] at ht
    simpa [boxMeasure_wired, criticalFKParameters, fkParameters] using ht
  let μ : Fin (q + 1) → Measure (SpinSpace q) := fun i => (μP i).toMeasure
  have hμall (i : Fin (q + 1)) :
      IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i) := by
    cases i using Fin.cases with
    | zero => simpa [μ] using hμ₀
    | succ k => simpa [μ] using hμp k
  have hdistinct := critical_potts_limits_pairwise_distinct q hq μP φ₀ φp
    hRC₀ hμ₀ hRCp hμp (lam₀ + 2 * S₀) hpositive₀ hrate₀
  have hnotAverage := critical_potts_free_measure_ne_wired_average q hq μP φ₀ φp
    hRC₀ hμ₀ hRCp hμp (lam₀ + 2 * S₀) hpositive₀ hrate₀
  have herg₀ : IsTranslationErgodic (μ 0) := by
    have hsampler := freeColoringMap_isFreeESC q hq φ₀ hno
    let samplerMeasure : Measure (SpinSpace q) :=
      (φ₀.toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))))).map
          (clusterColoring (⟨1, le_rfl, by omega⟩ : Set.Icc 1 q))
    have : IsProbabilityMeasure samplerMeasure := hsampler.1
    let samplerPM : ProbabilityMeasure (SpinSpace q) := ⟨samplerMeasure, inferInstance⟩
    have hreal (A : Finset Vertex) (ξ : SpinSpace q) :
        samplerPM.toMeasure.real (spinCylinder q A ξ) =
          (μP 0).toMeasure.real (spinCylinder q A ξ) := by
      simpa [samplerPM, samplerMeasure] using
        (hsampler.2 A ξ).trans (hES₀.2 A ξ).symm
    have hPM := probabilityMeasure_eq_of_spinCylinder_real q hq2 samplerPM (μP 0) hreal
    have hfactor := clusterColoring_map_ergodic_of_RCmixing
      (criticalFKParameters q hq) 0 φ₀.toMeasure hRC₀
      (⟨1, le_rfl, by omega⟩ : Set.Icc 1 q)
    have hmeasure : samplerPM.toMeasure = μ 0 := by
      simpa [μ] using congrArg ProbabilityMeasure.toMeasure hPM
    rw [← hmeasure]
    simpa [samplerPM, samplerMeasure] using hfactor
  have hergp (k : Fin q) : IsTranslationErgodic (μ k.succ) := by
    have hi : 1 ≤ (k.succ : ℕ) := by simp
    have hsampler := wiredColoringMap_isWiredESC q hq (φp k) k.succ hi
    let c₀ : Set.Icc 1 q := boundaryColor q k.succ hi
    let samplerMeasure : Measure (SpinSpace q) :=
      (φp k).toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))) |>.map
          (clusterColoring c₀)
    have : IsProbabilityMeasure samplerMeasure := hsampler.1
    let samplerPM : ProbabilityMeasure (SpinSpace q) := ⟨samplerMeasure, inferInstance⟩
    have hreal (A : Finset Vertex) (ξ : SpinSpace q) :
        samplerPM.toMeasure.real (spinCylinder q A ξ) =
          (μP k.succ).toMeasure.real (spinCylinder q A ξ) := by
      simpa [samplerPM, samplerMeasure, c₀] using
        (hsampler.2 A ξ).trans ((hESp k).2 A ξ).symm
    have hPM := probabilityMeasure_eq_of_spinCylinder_real q hq2 samplerPM
      (μP k.succ) hreal
    have hfactor := clusterColoring_map_ergodic_of_RCmixing
      (criticalFKParameters q hq) 1 (φp k).toMeasure (hRCp k) c₀
    have hmeasure : samplerPM.toMeasure = μ k.succ := by
      simpa [μ] using congrArg ProbabilityMeasure.toMeasure hPM
    rw [← hmeasure]
    simpa [samplerPM, samplerMeasure, c₀] using hfactor
  have hErgodic (i : Fin (q + 1)) : IsTranslationErgodic (μ i) := by
    cases i using Fin.cases with
    | zero => exact herg₀
    | succ k => exact hergp k
  have honeSite (k : Fin q) :
      (1 : ℝ) / q < (μ k.succ).real
        {σ | ((σ (0, 0) : ℕ)) = (k.succ : ℕ)} := by
    have hi : 1 ≤ (k.succ : ℕ) := by simp
    have hpos : 0 < (φp k).toMeasure.real
        {ω | clusterIsInfinite (rcInfiniteOpenGraph ω) (0, 0)} := by
      exact ENNReal.toReal_pos (hdisc k).2.ne' (measure_ne_top _ _)
    simpa [μ] using wired_pinned_one_site_probability_gt q hq2
      (pottsCriticalBeta q) hβ k.succ hi (φp k) (hφpweak k)
      (μP k.succ) (hμp k) hpos
  refine ⟨μ, hμall, ?_⟩
  refine ⟨⟨hdistinct, hErgodic, hnotAverage⟩, ?_⟩
  refine ⟨honeSite, ?_⟩
  intro lam hlam hcosh
  obtain ⟨S, hseries, hrate, hpositive⟩ :=
    hRCrate lam hlam hcosh φ₀.toMeasure hRC₀external
  have hspinRate := free_spin_rate_of_rc_rate q hq2 (pottsCriticalBeta q) hβ
    φ₀ hφ₀weak hRC₀ (μP 0) hμ₀ (lam + 2 * S) hrate
  exact ⟨S, hseries, by simpa [μ] using hspinRate, hpositive⟩

end PottsDiscontinuity.PottsThm
