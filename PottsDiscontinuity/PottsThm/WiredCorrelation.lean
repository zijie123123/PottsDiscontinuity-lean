module

public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability
public import PottsDiscontinuity.Potts.PartitionExpectationAlgebra
public import PottsDiscontinuity.Potts.SpinEventDecomposition
public import PottsDiscontinuity.Potts.WiredSpinObservations
public import PottsDiscontinuity.RCInfinite.ClusterEvents

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology
open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open Classical

noncomputable section

def pairClassLabel : Option Bool → Bool
  | none => false
  | some _ => true

def falsePinClassLabel : Option Bool → Bool
  | some true => true
  | _ => false

def truePinClassLabel : Option Bool → Bool
  | some false => true
  | _ => false

def pairClassRel : Setoid (Option Bool) := Setoid.ker pairClassLabel
def falsePinClassRel : Setoid (Option Bool) := Setoid.ker falsePinClassLabel
def truePinClassRel : Setoid (Option Bool) := Setoid.ker truePinClassLabel

private theorem natCard_quotient_ker_bool_of_surjective
    (f : Option Bool → Bool) (hf : Function.Surjective f) :
    Nat.card (Quotient (Setoid.ker f)) = 2 := by
  calc
    Nat.card (Quotient (Setoid.ker f)) = Nat.card (Set.range f) :=
      Nat.card_congr (Setoid.quotientKerEquivRange f)
    _ = Nat.card Bool := by rw [Set.range_eq_univ.mpr hf]; simp
    _ = 2 := by simp

private theorem natCard_quotient_top_optionBool :
    Nat.card (Quotient (⊤ : Setoid (Option Bool))) = 1 := by
  let : Subsingleton (Quotient (⊤ : Setoid (Option Bool))) :=
    Quotient.subsingleton_iff.mpr rfl
  let : Nonempty (Quotient (⊤ : Setoid (Option Bool))) := ⟨Quotient.mk _ none⟩
  exact Nat.card_unique

private theorem natCard_quotient_bot_optionBool :
    Nat.card (Quotient (⊥ : Setoid (Option Bool))) = 3 := by
  calc
    Nat.card (Quotient (⊥ : Setoid (Option Bool))) = Nat.card (Option Bool) :=
      Nat.card_congr (Setoid.quotientBotEquiv : Quotient (⊥ : Setoid (Option Bool)) ≃ Option Bool)
    _ = 3 := by norm_num

private theorem pinnedObservedClassCount (R : Setoid (Option Bool)) :
    observedClassCount R (markedMap some none) = Nat.card (Quotient R) := by
  have hid : markedMap some none = (id : Option Bool → Option Bool) := by
    funext a
    cases a <;> rfl
  rw [hid]
  rfl

private theorem pairClassRel_card : Nat.card (Quotient pairClassRel) = 2 := by
  exact natCard_quotient_ker_bool_of_surjective pairClassLabel (by
    intro b
    cases b
    · exact ⟨none, rfl⟩
    · exact ⟨some false, rfl⟩)

private theorem falsePinClassRel_card : Nat.card (Quotient falsePinClassRel) = 2 := by
  exact natCard_quotient_ker_bool_of_surjective falsePinClassLabel (by
    intro b
    cases b
    · exact ⟨none, rfl⟩
    · exact ⟨some true, rfl⟩)

private theorem truePinClassRel_card : Nat.card (Quotient truePinClassRel) = 2 := by
  exact natCard_quotient_ker_bool_of_surjective truePinClassLabel (by
    intro b
    cases b
    · exact ⟨none, rfl⟩
    · exact ⟨some false, rfl⟩)

private theorem pairClassRel_kernel (q : ℕ)
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability pairClassRel some (fun _ : Bool => c) none pin =
      (q : ℝ)⁻¹ := by
  have hcomp : pairClassRel.comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) := by
    intro a b hab
    change pairClassLabel (markedMap some none a) = pairClassLabel (markedMap some none b) at hab
    change markedMap (fun _ : Bool => c) pin a = markedMap (fun _ : Bool => c) pin b
    cases a <;> cases b <;> simp_all [pairClassLabel, markedMap]
  unfold pinnedClusterCylinderProbability
  rw [ite_eq_left hcomp, pinnedObservedClassCount, pairClassRel_card]
  simp

private theorem falsePinClassRel_compatible_iff (q : ℕ) (c pin : Set.Icc 1 q) :
    falsePinClassRel.comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) ↔ c = pin := by
  constructor
  · intro h
    have hrel : falsePinClassRel.comap (markedMap some none) (some false) none := by
      change falsePinClassLabel (markedMap some none (some false)) =
        falsePinClassLabel (markedMap some none none)
      rfl
    have heq := h hrel
    change markedMap (fun _ : Bool => c) pin (some false) =
      markedMap (fun _ : Bool => c) pin none at heq
    simpa [markedMap] using heq
  · intro hcp a b hab
    change falsePinClassLabel (markedMap some none a) =
      falsePinClassLabel (markedMap some none b) at hab
    change markedMap (fun _ : Bool => c) pin a = markedMap (fun _ : Bool => c) pin b
    cases a <;> cases b <;> simp_all [falsePinClassLabel, markedMap]

private theorem truePinClassRel_compatible_iff (q : ℕ) (c pin : Set.Icc 1 q) :
    truePinClassRel.comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) ↔ c = pin := by
  constructor
  · intro h
    have hrel : truePinClassRel.comap (markedMap some none) (some true) none := by
      change truePinClassLabel (markedMap some none (some true)) =
        truePinClassLabel (markedMap some none none)
      rfl
    have heq := h hrel
    change markedMap (fun _ : Bool => c) pin (some true) =
      markedMap (fun _ : Bool => c) pin none at heq
    simpa [markedMap] using heq
  · intro hcp a b hab
    change truePinClassLabel (markedMap some none a) =
      truePinClassLabel (markedMap some none b) at hab
    change markedMap (fun _ : Bool => c) pin a = markedMap (fun _ : Bool => c) pin b
    cases a <;> cases b <;> simp_all [truePinClassLabel, markedMap]

private theorem falsePinClassRel_kernel (q : ℕ)
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability falsePinClassRel some (fun _ : Bool => c) none pin =
      if c = pin then (q : ℝ)⁻¹ else 0 := by
  by_cases hcp : c = pin
  · have hcomp := (falsePinClassRel_compatible_iff q c pin).2 hcp
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left hcomp, pinnedObservedClassCount, falsePinClassRel_card]
    simp [hcp]
  · have hcomp : ¬ falsePinClassRel.comap (markedMap some none) ≤
        Setoid.ker (markedMap (fun _ : Bool => c) pin) :=
      fun hh => hcp ((falsePinClassRel_compatible_iff q c pin).1 hh)
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_right hcomp]
    simp [hcp]

private theorem truePinClassRel_kernel (q : ℕ)
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability truePinClassRel some (fun _ : Bool => c) none pin =
      if c = pin then (q : ℝ)⁻¹ else 0 := by
  by_cases hcp : c = pin
  · have hcomp := (truePinClassRel_compatible_iff q c pin).2 hcp
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left hcomp, pinnedObservedClassCount, truePinClassRel_card]
    simp [hcp]
  · have hcomp : ¬ truePinClassRel.comap (markedMap some none) ≤
        Setoid.ker (markedMap (fun _ : Bool => c) pin) :=
      fun hh => hcp ((truePinClassRel_compatible_iff q c pin).1 hh)
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_right hcomp]
    simp [hcp]

private theorem pairClassRel_kernel_sum (q : ℕ) (hq : 2 ≤ q)
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability pairClassRel some (fun _ : Bool => c) none pin = 1 := by
  simp_rw [pairClassRel_kernel q pin]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hcard : Fintype.card (Set.Icc 1 q) = q := by
    simp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard]
  field_simp

private theorem falsePinClassRel_kernel_sum (q : ℕ)
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability falsePinClassRel some (fun _ : Bool => c) none pin =
        (q : ℝ)⁻¹ := by
  simp_rw [falsePinClassRel_kernel q pin]
  simp

private theorem truePinClassRel_kernel_sum (q : ℕ)
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability truePinClassRel some (fun _ : Bool => c) none pin =
        (q : ℝ)⁻¹ := by
  simp_rw [truePinClassRel_kernel q pin]
  simp

private theorem top_optionBool_compatible_iff (q : ℕ) (c pin : Set.Icc 1 q) :
    (⊤ : Setoid (Option Bool)).comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) ↔ c = pin := by
  constructor
  · intro h
    have hrel : (⊤ : Setoid (Option Bool)).comap (markedMap some none) (some false) none := by
      trivial
    have heq := h hrel
    change markedMap (fun _ : Bool => c) pin (some false) =
      markedMap (fun _ : Bool => c) pin none at heq
    simpa [markedMap] using heq
  · intro hcp a b hab
    change True at hab
    change markedMap (fun _ : Bool => c) pin a = markedMap (fun _ : Bool => c) pin b
    cases a <;> cases b <;> simp [markedMap, hcp]

private theorem top_optionBool_kernel (q : ℕ)
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability (⊤ : Setoid (Option Bool)) some
      (fun _ : Bool => c) none pin = if c = pin then 1 else 0 := by
  by_cases hcp : c = pin
  · have hcomp := (top_optionBool_compatible_iff q c pin).2 hcp
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left hcomp, pinnedObservedClassCount, natCard_quotient_top_optionBool]
    simp [hcp]
  · have hcomp : ¬ (⊤ : Setoid (Option Bool)).comap (markedMap some none) ≤
        Setoid.ker (markedMap (fun _ : Bool => c) pin) :=
      fun hh => hcp ((top_optionBool_compatible_iff q c pin).1 hh)
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_right hcomp]
    simp [hcp]

private theorem top_optionBool_kernel_sum (q : ℕ)
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability (⊤ : Setoid (Option Bool)) some
        (fun _ : Bool => c) none pin = 1 := by
  simp_rw [top_optionBool_kernel q pin]
  simp

private theorem bot_optionBool_compatible (q : ℕ) (c pin : Set.Icc 1 q) :
    (⊥ : Setoid (Option Bool)).comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) := by
  intro a b hab
  change markedMap (fun _ : Bool => c) pin a = markedMap (fun _ : Bool => c) pin b
  have hab' : a = b := by
    have hid : markedMap some none = (id : Option Bool → Option Bool) := by
      funext z
      cases z <;> rfl
    rw [hid] at hab
    exact hab
  rw [hab']

private theorem bot_optionBool_kernel (q : ℕ)
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability (⊥ : Setoid (Option Bool)) some
      (fun _ : Bool => c) none pin = ((q : ℝ) ^ 2)⁻¹ := by
  have hcomp := bot_optionBool_compatible q c pin
  unfold pinnedClusterCylinderProbability
  rw [ite_eq_left hcomp, pinnedObservedClassCount, natCard_quotient_bot_optionBool]
  simp

private theorem bot_optionBool_kernel_sum (q : ℕ) (hq : 2 ≤ q)
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability (⊥ : Setoid (Option Bool)) some
        (fun _ : Bool => c) none pin = (q : ℝ)⁻¹ := by
  simp_rw [bot_optionBool_kernel q pin]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hcard : Fintype.card (Set.Icc 1 q) = q := by
    simp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard]
  field_simp

private theorem wiredRelation_eq_top (R : Setoid (Option Bool))
    (hxy : R (some false) (some true)) (hxg : R (some false) none) : R = ⊤ := by
  have hyg : R (some true) none := R.trans (R.symm hxy) hxg
  apply top_unique
  intro a b _
  cases a with
  | none =>
    cases b with
    | none => exact R.refl _
    | some b =>
      cases b with
      | false => exact R.symm hxg
      | true => exact R.symm hyg
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => exact hxg
      | some b =>
        cases b with
        | false => exact R.refl _
        | true => exact hxy
    | true =>
      cases b with
      | none => exact hyg
      | some b =>
        cases b with
        | false => exact R.symm hxy
        | true => exact R.refl _

private theorem wiredRelation_eq_pairClassRel (R : Setoid (Option Bool))
    (hxy : R (some false) (some true)) (hxg : ¬ R (some false) none) :
    R = pairClassRel := by
  have hyg : ¬ R (some true) none := by
    intro h
    exact hxg (R.trans hxy h)
  have hgnx : ¬ R none (some false) := fun h => hxg (R.symm h)
  have hgny : ¬ R none (some true) := fun h => hyg (R.symm h)
  have hyx : R (some true) (some false) := R.symm hxy
  apply Setoid.ext
  intro a b
  change R a b ↔ pairClassLabel a = pairClassLabel b
  cases a with
  | none =>
    cases b with
    | none => simp [pairClassLabel]
    | some b =>
      cases b <;> simp [pairClassLabel, hgnx, hgny]
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => simp [pairClassLabel, hxg]
      | some b =>
        cases b with
        | false => simp [pairClassLabel]
        | true => simp [pairClassLabel, hxy]
    | true =>
      cases b with
      | none => simp [pairClassLabel, hyg]
      | some b =>
        cases b with
        | false => simp [pairClassLabel, hyx]
        | true => simp [pairClassLabel]

private theorem wiredRelation_eq_falsePinClassRel (R : Setoid (Option Bool))
    (hxy : ¬ R (some false) (some true)) (hxg : R (some false) none) :
    R = falsePinClassRel := by
  have hyg : ¬ R (some true) none := by
    intro h
    exact hxy (R.trans hxg (R.symm h))
  have hyx : ¬ R (some true) (some false) := fun h => hxy (R.symm h)
  have hgx : R none (some false) := R.symm hxg
  have hgy : ¬ R none (some true) := fun h => hyg (R.symm h)
  apply Setoid.ext
  intro a b
  change R a b ↔ falsePinClassLabel a = falsePinClassLabel b
  cases a with
  | none =>
    cases b with
    | none => simp [falsePinClassLabel]
    | some b =>
      cases b with
      | false => simp [falsePinClassLabel, hgx]
      | true => simp [falsePinClassLabel, hgy]
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => simp [falsePinClassLabel, hxg]
      | some b =>
        cases b with
        | false => simp [falsePinClassLabel]
        | true => simp [falsePinClassLabel, hxy]
    | true =>
      cases b with
      | none => simp [falsePinClassLabel, hyg]
      | some b =>
        cases b with
        | false => simp [falsePinClassLabel, hyx]
        | true => simp [falsePinClassLabel]

private theorem wiredRelation_eq_truePinClassRel (R : Setoid (Option Bool))
    (hxy : ¬ R (some false) (some true)) (hyg : R (some true) none) :
    R = truePinClassRel := by
  have hxg : ¬ R (some false) none := by
    intro h
    exact hxy (R.trans h (R.symm hyg))
  have hyx : ¬ R (some true) (some false) := fun h => hxy (R.symm h)
  have hgx : ¬ R none (some false) := fun h => hxg (R.symm h)
  have hgy : R none (some true) := R.symm hyg
  apply Setoid.ext
  intro a b
  change R a b ↔ truePinClassLabel a = truePinClassLabel b
  cases a with
  | none =>
    cases b with
    | none => simp [truePinClassLabel]
    | some b =>
      cases b with
      | false => simp [truePinClassLabel, hgx]
      | true => simp [truePinClassLabel, hgy]
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => simp [truePinClassLabel, hxg]
      | some b =>
        cases b with
        | false => simp [truePinClassLabel]
        | true => simp [truePinClassLabel, hxy]
    | true =>
      cases b with
      | none => simp [truePinClassLabel, hyg]
      | some b =>
        cases b with
        | false => simp [truePinClassLabel, hyx]
        | true => simp [truePinClassLabel]

private theorem wiredRelation_eq_bot (R : Setoid (Option Bool))
    (hxy : ¬ R (some false) (some true))
    (hxg : ¬ R (some false) none) (hyg : ¬ R (some true) none) : R = ⊥ := by
  apply bot_unique
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      cases b with
      | false => exact (hxg (R.symm hab)).elim
      | true => exact (hyg (R.symm hab)).elim
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => exact (hxg hab).elim
      | some b =>
        cases b with
        | false => rfl
        | true => exact (hxy hab).elim
    | true =>
      cases b with
      | none => exact (hyg hab).elim
      | some b =>
        cases b with
        | false => exact (hxy (R.symm hab)).elim
        | true => rfl

private theorem wiredPairSetoid_cases (R : Setoid (Option Bool)) :
    R = (⊤ : Setoid (Option Bool)) ∨ R = pairClassRel ∨
      R = falsePinClassRel ∨ R = truePinClassRel ∨ R = ⊥ := by
  by_cases hxy : R (some false) (some true)
  · by_cases hxg : R (some false) none
    · exact Or.inl (wiredRelation_eq_top R hxy hxg)
    · exact Or.inr (Or.inl (wiredRelation_eq_pairClassRel R hxy hxg))
  · by_cases hxg : R (some false) none
    · exact Or.inr (Or.inr (Or.inl (wiredRelation_eq_falsePinClassRel R hxy hxg)))
    · by_cases hyg : R (some true) none
      · exact Or.inr (Or.inr (Or.inr (Or.inl (wiredRelation_eq_truePinClassRel R hxy hyg))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (wiredRelation_eq_bot R hxy hxg hyg))))

private theorem wired_two_point_kernel_sum (q : ℕ) (hq : 2 ≤ q)
    (pin : Set.Icc 1 q) (R : Setoid (Option Bool)) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
        1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
          (if R (some false) (some true) ∨
            (R (some false) none ∧ R (some true) none) then 1 else 0) := by
  rcases wiredPairSetoid_cases R with htop | hpair | hfalse | htrue | hbot
  · rw [htop]
    have hxy : (⊤ : Setoid (Option Bool)) (some false) (some true) := by trivial
    rw [top_optionBool_kernel_sum q pin]
    simp [hxy]
  · rw [hpair]
    have hxy : pairClassRel (some false) (some true) := by
      change pairClassLabel (some false) = pairClassLabel (some true)
      rfl
    rw [pairClassRel_kernel_sum q hq pin]
    simp [hxy]
  · rw [hfalse]
    have hxy : ¬ falsePinClassRel (some false) (some true) := by
      change ¬ (falsePinClassLabel (some false) = falsePinClassLabel (some true))
      simp [falsePinClassLabel]
    have hxg : falsePinClassRel (some false) none := by
      change falsePinClassLabel (some false) = falsePinClassLabel none
      rfl
    have hyg : ¬ falsePinClassRel (some true) none := by
      change ¬ (falsePinClassLabel (some true) = falsePinClassLabel none)
      simp [falsePinClassLabel]
    rw [falsePinClassRel_kernel_sum q pin]
    simp [hxy, hxg, hyg]
  · rw [htrue]
    have hxy : ¬ truePinClassRel (some false) (some true) := by
      change ¬ (truePinClassLabel (some false) = truePinClassLabel (some true))
      simp [truePinClassLabel]
    have hxg : ¬ truePinClassRel (some false) none := by
      change ¬ (truePinClassLabel (some false) = truePinClassLabel none)
      simp [truePinClassLabel]
    have hyg : truePinClassRel (some true) none := by
      change truePinClassLabel (some true) = truePinClassLabel none
      rfl
    rw [truePinClassRel_kernel_sum q pin]
    simp [hxy, hxg, hyg]
  · rw [hbot]
    have hxy : ¬ (⊥ : Setoid (Option Bool)) (some false) (some true) := by
      simp
    have hxg : ¬ (⊥ : Setoid (Option Bool)) (some false) none := by
      simp
    have hyg : ¬ (⊥ : Setoid (Option Bool)) (some true) none := by
      simp
    rw [bot_optionBool_kernel_sum q hq pin]
    simp

/-- Edwards--Sokal coloring gives a wired two-spin lower bound: the spins are
equal whenever the observations are connected, and in particular are equal
with certainty when both observations lie in infinite clusters. -/
theorem wired_spin_correlation_lower_bound (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure (fkParameters q hq β hβ)
      (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (x y : LatticeVertex) :
    μ.toMeasure.real {σ | σ x = σ y} ≥
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        φ.toMeasure.real (infiniteAt x ∩ infiniteAt y) := by
  let v : Bool → LatticeVertex := fun b => if b then y else x
  let pin := boundaryColor q i hi
  let r : LatticeConfiguration → Setoid (Option Bool) :=
    infiniteWiredPartition (Option.map v)
  let P : Setoid (Option Bool) → Prop := fun R =>
    R (some false) (some true) ∨ (R (some false) none ∧ R (some true) none)
  have hevent (c : Set.Icc 1 q) :
      {σ : SpinSpace q | σ x = c ∧ σ y = c} =
        spinObservationEvent q v (fun _ => c) := by
    ext σ
    simp [spinObservationEvent, v]
  have hformula (c : Set.Icc 1 q) :
      μ.toMeasure.real {σ : SpinSpace q | σ x = c ∧ σ y = c} =
        partitionExpectation φ.toMeasure r
          (fun R => pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin) := by
    rw [hevent c]
    exact wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v (fun _ => c)
  let : IsProbabilityMeasure μ.toMeasure := hμ.1
  have hsum_colors := measureReal_same_colour_sum μ.toMeasure
    (fun σ : SpinSpace q => σ x) (fun σ => σ y)
    (measurable_pi_apply x) (measurable_pi_apply y)
  have hsum_kernel :
      (∑ c : Set.Icc 1 q,
        partitionExpectation φ.toMeasure r
          (fun R => pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin)) =
        partitionExpectation φ.toMeasure r
          (fun R => ∑ c : Set.Icc 1 q,
            pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin) := by
    unfold partitionExpectation
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro R hR
    rw [← Finset.mul_sum]
  have hkernel : (fun R : Setoid (Option Bool) =>
      ∑ c : Set.Icc 1 q,
        pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin) =
      fun R => 1 / (q : ℝ) + (1 - 1 / (q : ℝ)) * (if P R then 1 else 0) := by
    funext R
    exact wired_two_point_kernel_sum q hq pin R
  have hrelation_event : {ω | P (r ω)} =
      {ω | (rcInfiniteOpenGraph ω).Reachable x y ∨
        (ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y)} := by
    ext ω
    change (infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) (some y) ∨
      (infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) none ∧
        infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some y) none)) ↔ _
    rw [infiniteMergedSetoid_some_some, infiniteMergedSetoid_some_none,
      infiniteMergedSetoid_some_none]
    simp [RCInfinite.infiniteAt, RCInfinite.cluster, clusterIsInfinite]
  have hformula' : μ.toMeasure.real {σ | σ x = σ y} =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        φ.toMeasure.real {ω | P (r ω)} := by
    rw [hsum_colors]
    simp_rw [hformula]
    rw [hsum_kernel, hkernel]
    calc
      _ = partitionExpectation φ.toMeasure r (fun R =>
          1 / (q : ℝ) + (1 - 1 / (q : ℝ)) * (if P R then 1 else 0)) := by
        congr 1
      _ = _ := by
        convert (partitionExpectation_affine_indicator φ.toMeasure r
          (infiniteWiredPartition_measurableSet (Option.map v)) P
          (1 / (q : ℝ)) (1 - 1 / (q : ℝ))) using 1
        congr 1
        funext R
        by_cases hR : P R <;> simp [hR]
  rw [hrelation_event] at hformula'
  have hmass := measureReal_mono (μ := φ.toMeasure)
    (show {ω : LatticeConfiguration | ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y} ⊆
      {ω | (rcInfiniteOpenGraph ω).Reachable x y ∨
        (ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y)} from by
          intro ω hω
          exact Or.inr hω)
  have hcoef : 0 ≤ 1 - 1 / (q : ℝ) := by
    have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    have hqRpos : (0 : ℝ) < (q : ℝ) := by linarith
    have hfrac : (1 : ℝ) / (q : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hqRpos]
      nlinarith
    linarith
  calc
    μ.toMeasure.real {σ | σ x = σ y} =
        1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
          φ.toMeasure.real {ω | (rcInfiniteOpenGraph ω).Reachable x y ∨
            (ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y)} := hformula'
    _ ≥ 1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
          φ.toMeasure.real (infiniteAt x ∩ infiniteAt y) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (mul_le_mul_of_nonneg_left hmass hcoef) (1 / (q : ℝ))

end
end PottsDiscontinuity.PottsThm
