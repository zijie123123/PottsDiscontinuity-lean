module

public import PottsDiscontinuity.TorusRC.SquareBoxComparison
public import PottsDiscontinuity.TorusRC.FiniteEventMeasure

/-! # Cofinal native squares recover the exact rotated free connection probability -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusRC

open CorrLength FK

theorem rotatedDiagonalProbability_pos (θ : Parameters) (n : ℕ) :
    0 < ((rotatedDiagonalConnectionProbability θ n : NNReal):ℝ) := by
  rw [rotatedDiagonalConnectionProbability_eq]
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  exact freeBoxLimit_connection_positive θ _ _

/-- Every strict lower bound on the infinite-volume connection probability
`rotatedDiagonalConnectionProbability` (`CorrLength/RotatedFreeLimit.lean`)
holds eventually for the native square free-box probabilities. Only cofinal
domain inclusion and the proved free-box exhaustion theorem
`FK.freeBoxLimit_existsUnique` are used. -/
theorem liftedBoxFreeDiagonalProbability_eventually_gt (θ : Parameters) (n : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (htp : t < ((rotatedDiagonalConnectionProbability θ n : NNReal):ℝ)) :
    ∀ᶠ R in atTop, t < liftedBoxFreeConnectionProbability θ rotatedLatticeOrigin R
      rotatedLatticeOrigin (rotatedDiagonalSite n) := by
  let ν : ProbabilityMeasure LatticeConfiguration := Classical.choose (freeBoxLimit_existsUnique θ)
  have hweak : Tendsto (fun r => boxProbabilityMeasure θ (0,0) r) atTop (𝓝 ν) :=
    (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1 (fun _ => (0,0)) (fun r => r)
      origin_latticeBox_nested origin_latticeBox_exhaustive
  have hp : t < ν.toMeasure.real (connectionEvent (0,0) ((n:ℤ),(n:ℤ))) := by
    rw [rotatedDiagonalConnectionProbability_eq] at htp
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using htp
  have hevent := open_probability_eventually_gt _ ν hweak
    (connectionEvent (0,0) ((n:ℤ),(n:ℤ))) (connectionEvent_isOpen _ _) t ht hp
  obtain ⟨r,hr,hrn⟩ := (hevent.and (eventually_ge_atTop n)).exists
  have hu : (0,0) ∈ latticeBox (0,0) r := center_mem_latticeBox _ _
  have hv : ((n:ℤ),(n:ℤ)) ∈ latticeBox (0,0) r := by
    rw [mem_latticeBox]
    dsimp
    constructor <;> constructor <;> omega
  let u : BoxVertex (0,0) r := ⟨(0,0),hu⟩
  let v : BoxVertex (0,0) r := ⟨((n:ℤ),(n:ℤ)),hv⟩
  have hprob := boxProbabilityMeasure_connection_eq θ (0,0) r u v
  have hru : squareToRotatedVertex u.val = rotatedLatticeOrigin := by
    apply Subtype.ext
    rfl
  have hrv : squareToRotatedVertex v.val = rotatedDiagonalSite n := by
    apply Subtype.ext
    ext <;> dsimp [squareToRotatedVertex,v,rotatedDiagonalSite] <;> ring
  filter_upwards [eventually_ge_atTop (2*r)] with R hR
  have hcomp := squareBox_connection_probability_le_native θ r R hR u v
  rw [hru,hrv,← hprob] at hcomp
  exact hr.trans_le hcomp

end PottsDiscontinuity.TorusRC
