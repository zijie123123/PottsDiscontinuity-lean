module

public import PottsDiscontinuity.Potts.FreeSpinObservations
public import PottsDiscontinuity.Potts.WiredSpinFormula

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open Classical

private lemma optionUnit_setoid_top (R : Setoid (Option PUnit))
    (h : R (some PUnit.unit) none) : R = ⊤ := by
  apply top_unique
  intro a b _
  cases a with
  | none =>
    cases b with
    | none => exact R.refl _
    | some b => cases b; exact R.symm h
  | some a =>
    cases a
    cases b with
    | none => exact h
    | some b => cases b; exact R.refl _

private lemma optionUnit_setoid_bot (R : Setoid (Option PUnit))
    (h : ¬ R (some PUnit.unit) none) : R = ⊥ := by
  apply bot_unique
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => cases b; exact (h (R.symm hab)).elim
  | some a =>
    cases a
    cases b with
    | none => exact (h hab).elim
    | some b => cases b; rfl

private lemma card_optionUnit_quotient_bot :
    Nat.card (Quotient (⊥ : Setoid (Option PUnit))) = 2 := by
  calc
    Nat.card (Quotient (⊥ : Setoid (Option PUnit))) = Nat.card (Option PUnit) :=
      Nat.card_congr (Setoid.quotientBotEquiv : Quotient (⊥ : Setoid (Option PUnit)) ≃ Option PUnit)
    _ = 2 := by norm_num

private lemma wired_one_point_kernel_off_pin (q : ℕ)
    (R : Setoid (Option PUnit)) (pin color : Set.Icc 1 q) (hcolor : color ≠ pin) :
    pinnedClusterCylinderProbability R some (fun _ : PUnit => color) none pin =
      if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹ := by
  classical
  have hid : markedMap some none = (id : Option PUnit → Option PUnit) := by
    funext a
    cases a <;> rfl
  have hcount : observedClassCount R (markedMap some none) = Nat.card (Quotient R) := by
    rw [hid]
    rfl
  by_cases h : R (some PUnit.unit) none
  · have htop : R = ⊤ := optionUnit_setoid_top R h
    have hcompat : ¬ R.comap (markedMap some none) ≤
        Setoid.ker (markedMap (fun _ : PUnit => color) pin) := by
      intro hle
      have hrel : R.comap (markedMap some none) (some PUnit.unit) none := by
        change R (markedMap some none (some PUnit.unit)) (markedMap some none none)
        simpa [markedMap] using h
      have heq := hle hrel
      exact hcolor heq
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_right hcompat, ite_eq_left h]
  · have hbot : R = ⊥ := optionUnit_setoid_bot R h
    have hcompat : R.comap (markedMap some none) ≤
        Setoid.ker (markedMap (fun _ : PUnit => color) pin) := by
      rw [hbot]
      intro a b hab
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b => cases b; simp [markedMap] at hab
      | some a =>
        cases a
        cases b with
        | none => simp [markedMap] at hab
        | some b => cases b; rfl
    have hcount' : observedClassCount R (markedMap some none) = 2 := by
      rw [hcount, hbot, card_optionUnit_quotient_bot]
    rw [pinnedClusterCylinderProbability, ite_eq_left hcompat, hcount', card_pottsColors]
    rw [ite_eq_right h]
    norm_num

/-- At a wired Potts limit, a non-pinned colour at one site has probability at
most `1/q`. -/
theorem wired_off_color_probability_le_uniform (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (x : ℤ × ℤ) (color : Set.Icc 1 q)
    (hcolor : color ≠ boundaryColor q i hi) :
    μ.toMeasure.real {σ | σ x = color} ≤ 1 / (q : ℝ) := by
  let v : Unit → ℤ × ℤ := fun _ => x
  let ξ : Unit → Set.Icc 1 q := fun _ => color
  have hevent : {σ : SpinSpace q | σ x = color} =
      spinObservationEvent (A := PUnit) q v ξ := by
    ext σ
    simp [spinObservationEvent, v, ξ]
  rw [hevent, wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v ξ]
  let r : LatticeConfiguration → Setoid (Option Unit) :=
    infiniteWiredPartition (Option.map v)
  have hkernel (R : Setoid (Option Unit)) :
      pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi) =
        if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹ := by
    exact wired_one_point_kernel_off_pin q R (boundaryColor q i hi) color hcolor
  change partitionExpectation φ.toMeasure r
      (fun R => pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)) ≤ _
  rw [show (fun R : Setoid (Option Unit) =>
      pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)) =
      fun R => if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹ from funext hkernel]
  have hevent' : {ω | r ω (some PUnit.unit) none} =
      {ω | clusterIsInfinite (rcInfiniteOpenGraph ω) x} := by
    ext ω
    change infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) none ↔ _
    exact infiniteMergedSetoid_some_none _ _
  have hpart := partitionExpectation_affine_indicator φ.toMeasure r
    (infiniteWiredPartition_measurableSet (Option.map v))
    (fun R => ¬ R (some PUnit.unit) none) 0 (1 / (q : ℝ))
  have hkernel_affine :
      (fun R : Setoid (Option Unit) => if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹) =
        fun R => 0 + (1 / (q : ℝ)) * (if ¬ R (some PUnit.unit) none then 1 else 0) := by
    funext R
    by_cases hR : R (some PUnit.unit) none <;> simp [hR]
  have hprob : φ.toMeasure.real {ω | ¬ r ω (some PUnit.unit) none} ≤ 1 := by
    have hle := ProbabilityMeasure.apply_le_one φ {ω | ¬ r ω (some PUnit.unit) none}
    exact_mod_cast hle
  calc
    partitionExpectation φ.toMeasure r
        (fun R => if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹) =
        (1 / (q : ℝ)) * φ.toMeasure.real {ω | ¬ r ω (some PUnit.unit) none} := by
      rw [hkernel_affine]
      simpa using hpart
    _ ≤ 1 / (q : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hprob (by positivity : 0 ≤ 1 / (q : ℝ))

/-- A free Edwards--Sokal limit has a uniform one site marginal. -/
theorem free_one_site_probability (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (x : ℤ × ℤ) (color : Set.Icc 1 q) :
    μ.toMeasure.real {σ | σ x = color} = 1 / (q : ℝ) := by
  let v : Unit → ℤ × ℤ := fun _ => x
  let ξ : Unit → Set.Icc 1 q := fun _ => color
  have hevent : {σ : SpinSpace q | σ x = color} =
      spinObservationEvent (A := Unit) q v ξ := by
    ext σ
    simp [spinObservationEvent, v, ξ]
  rw [hevent, free_spin_observation_formula (A := Unit) q hq β hβ φ hφ μ hμ v ξ]
  let r : LatticeConfiguration → Setoid Unit := infiniteFreePartition v
  have hkernel (R : Setoid Unit) :
      clusterCylinderProbability (A := Unit) (V := Unit) R id ξ = 1 / (q : ℝ) := by
    have hcomp : R.comap id ≤ Setoid.ker ξ := by
      intro a b _
      simp
    have hcount : observedClassCount (A := Unit) (V := Unit) R id = 1 := by
      rw [observedClassCount_eq_range]
      let f : Unit → Quotient R := Quotient.mk R
      let : Subsingleton (Set.range f) := by
        constructor
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        apply Subtype.ext
        exact Subsingleton.elim _ _
      let : Nonempty (Set.range f) := ⟨⟨f (), ⟨(), rfl⟩⟩⟩
      exact Nat.card_unique
    rw [clusterCylinderProbability, ite_eq_left hcomp, hcount, card_pottsColors]
    simp only [pow_one]
    simp [one_div]
  have hexpect : partitionExpectation φ.toMeasure r
      (fun R => clusterCylinderProbability (A := Unit) (V := Unit) R id ξ) =
        1 / (q : ℝ) := by
    rw [show (fun R : Setoid Unit =>
      clusterCylinderProbability (A := Unit) (V := Unit) R id ξ) =
      fun _ => 1 / (q : ℝ) from funext hkernel]
    unfold partitionExpectation
    rw [← Finset.sum_mul]
    rw [sum_partition_mass φ.toMeasure r
      (infiniteFreePartition_measurableSet v), one_mul]
  change partitionExpectation φ.toMeasure r
      (fun R => clusterCylinderProbability (A := Unit) (V := Unit) R id ξ) = _
  exact hexpect

/-- Positive wired percolation makes the pinned one site colour strictly more
likely than a uniform colour. -/
theorem wired_pinned_one_site_probability_gt (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure (fkParameters q hq β hβ)
      (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (hpos : 0 < φ.toMeasure.real
      {ω | clusterIsInfinite (rcInfiniteOpenGraph ω) (0, 0)}) :
    1 / (q : ℝ) < μ.toMeasure.real
      {σ | (σ (0, 0) : ℕ) = (i : ℕ)} := by
  rw [wired_origin_spin_probability q hq β hβ i hi φ hφ μ hμ]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hc : 0 < 1 - 1 / (q : ℝ) := by
    rw [sub_pos]
    exact (div_lt_one hqpos).2 (by exact_mod_cast (show 1 < q by omega))
  nlinarith [mul_pos hc hpos]

end PottsDiscontinuity.PottsThm
