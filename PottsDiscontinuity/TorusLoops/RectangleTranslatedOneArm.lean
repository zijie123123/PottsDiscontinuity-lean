module

public import PottsDiscontinuity.TorusLoops.RectangleInfiniteComparison
public import PottsDiscontinuity.TorusLoops.RectangleOneArmComparison

/-!
# Rooted one-arm probabilities in the canonical free limit

Finite free origin boxes are dominated by the free-limit probability of a
one-arm event rooted at any fixed lattice vertex. Translation invariance of the
free limit then identifies that probability with the origin one-arm probability.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.FK.Internal
open PottsDiscontinuity.Zhang

noncomputable section

/-- The coordinate one-arm event rooted at `a`, represented by translating the
configuration so that `a` becomes the origin. -/
def translatedOneArmEvent (a : LatticeVertex) (k : ℕ) : Set LatticeConfiguration :=
  (latticeConfigurationTranslationHomeomorph (-a)) ⁻¹' oneArmEvent k

/-- Translated finite-witness approximations to a rooted one-arm event. -/
def translatedFreeOneArmApprox (a : LatticeVertex) (k n : ℕ) :
    Set LatticeConfiguration :=
  (latticeConfigurationTranslationHomeomorph (-a)) ⁻¹' freeOneArmApprox k n

theorem translatedFreeOneArmApprox_mono (a : LatticeVertex) (k : ℕ) :
    Monotone (translatedFreeOneArmApprox a k) := by
  intro n m hnm ω hω
  exact freeOneArmApprox_mono k hnm hω

theorem translatedFreeOneArmApprox_isClopen (a : LatticeVertex) (k n : ℕ) :
    IsClopen (translatedFreeOneArmApprox a k n) :=
  (freeOneArmApprox_isClopen k n).preimage
    (latticeConfigurationTranslationHomeomorph (-a)).continuous

theorem translatedFreeOneArmApprox_isUpperSet (a : LatticeVertex) (k n : ℕ) :
    IsUpperSet (translatedFreeOneArmApprox a k n) := by
  intro ω η hωη hω
  change latticeConfigurationTranslate (-a) ω ∈ freeOneArmApprox k n at hω
  have htranslated : latticeConfigurationTranslate (-a) ω ≤
      latticeConfigurationTranslate (-a) η := by
    intro e
    rw [latticeConfigurationTranslate_apply, latticeConfigurationTranslate_apply]
    exact hωη _
  change latticeConfigurationTranslate (-a) η ∈ freeOneArmApprox k n
  exact freeOneArmApprox_isUpperSet k n htranslated hω

theorem iUnion_translatedFreeOneArmApprox (a : LatticeVertex) (k : ℕ) :
    (⋃ n, translatedFreeOneArmApprox a k n) = translatedOneArmEvent a k := by
  ext ω
  simp only [translatedFreeOneArmApprox, translatedOneArmEvent,
    Set.mem_iUnion, Set.mem_preimage]
  rw [← iUnion_freeOneArmApprox k]
  simp only [Set.mem_iUnion]

private theorem tendsto_translatedFreeOneArmApprox_probability
    (ν : ProbabilityMeasure LatticeConfiguration) (a : LatticeVertex) (k : ℕ) :
    Tendsto (fun n : ℕ => ν.toFiniteMeasure (translatedFreeOneArmApprox a k n)) atTop
      (𝓝 (ν.toFiniteMeasure (translatedOneArmEvent a k))) := by
  have hacc (n : ℕ) :
      Set.accumulate (translatedFreeOneArmApprox a k) n =
        translatedFreeOneArmApprox a k n := by
    ext ω
    rw [Set.mem_accumulate]
    constructor
    · rintro ⟨m, hmn, hm⟩
      exact translatedFreeOneArmApprox_mono a k hmn hm
    · intro hn
      exact ⟨n, le_rfl, hn⟩
  have h := ν.toFiniteMeasure.tendsto_measure_iUnion_accumulate
    (f := translatedFreeOneArmApprox a k)
  have h' : Tendsto
      (fun n => ν.toFiniteMeasure (translatedFreeOneArmApprox a k n)) atTop
      (𝓝 (ν.toFiniteMeasure (⋃ n, translatedFreeOneArmApprox a k n))) := by
    refine h.congr' ?_
    filter_upwards with n
    rw [← hacc n]
  simpa [ProbabilityMeasure.toFiniteMeasure_apply, iUnion_translatedFreeOneArmApprox] using h'

/-- Every free origin-box probability of a rooted one-arm event is bounded by
its probability in the canonical free limit. -/
theorem boxProbabilityMeasure_translatedOneArm_le_freeBoxLimit
    (q : Parameters) (r : ℕ) (a : LatticeVertex) (k : ℕ) :
    boxProbabilityMeasure q (0, 0) r (translatedOneArmEvent a k) ≤
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (translatedOneArmEvent a k) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  let ν : ProbabilityMeasure LatticeConfiguration := boxProbabilityMeasure q (0, 0) r
  have hbox := tendsto_translatedFreeOneArmApprox_probability ν a k
  have hlim := tendsto_translatedFreeOneArmApprox_probability μ a k
  have hle (n : ℕ) :
      ν (translatedFreeOneArmApprox a k n) ≤ μ (translatedFreeOneArmApprox a k n) :=
    freeBoxLimit_clopen_upper_ge_box q r (translatedFreeOneArmApprox a k n)
      (translatedFreeOneArmApprox_isClopen a k n)
      (translatedFreeOneArmApprox_isUpperSet a k n)
  have h := le_of_tendsto_of_tendsto' hbox hlim hle
  simpa only [Prod.forall, ge_iff_le, FiniteMeasure.self_eq_mass_mul_normalize,
      ProbabilityMeasure.mass_toFiniteMeasure, ProbabilityMeasure.toFiniteMeasure_normalize_eq_self,
      one_mul, ν, μ] using h

/-- Translation invariance identifies a rooted one-arm probability in the
canonical free limit with the probability rooted at the origin. -/
theorem freeBoxLimit_translatedOneArm_probability_eq (q : Parameters)
    (a : LatticeVertex) (k : ℕ) :
    (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (translatedOneArmEvent a k) =
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (oneArmEvent k) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  have hinv := freeBoxLimit_translation_invariant q (-a)
  have hinv' : ProbabilityMeasure.map μ
      (latticeConfigurationTranslationHomeomorph (-a)).toFun = μ := by
    simpa only [Prod.forall, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv,
        latticeConfigurationTranslate, μ] using hinv
  have hmap := ProbabilityMeasure.map_apply μ
    ((latticeConfigurationTranslationHomeomorph (-a)).continuous_toFun.measurable.aemeasurable)
    (measurableSet_oneArmEvent k)
  have hEval := congrArg
    (fun ν : ProbabilityMeasure LatticeConfiguration => ν (oneArmEvent k)) hinv'
  rw [hmap] at hEval
  simpa only [Prod.forall, translatedOneArmEvent, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv,
      μ] using hEval

end
end PottsDiscontinuity.TorusLoops
