module

public import PottsDiscontinuity.Potts.ClusterColoring

/-!
# Cylinder probabilities of independent component colourings

The probability of a prescribed finite spin pattern depends only on the
connection partition of its observed vertices. Pinning a distinguished class
is handled by adjoining one marked observation, without any uniqueness
assumption on components represented by that class.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

variable {A B V C : Type*}

/-- Functions extending a consistent pattern are freely chosen away from the
range of the observation map. -/
def functionExtensionsEquiv (f : A → B) (ξ : A → C) (hξ : ξ.FactorsThrough f) :
    {F : B → C // ∀ a, F (f a) = ξ a} ≃ ({b : B // b ∉ Set.range f} → C) := by
  let η : Set.range f → C := ξ ∘ Set.rangeSplitting f
  have hη (a : A) : η (Set.rangeFactorization f a) = ξ a :=
    hξ (Set.apply_rangeSplitting f (Set.rangeFactorization f a))
  refine (Equiv.subtypeEquivRight (fun F => ?_)).trans
    (Equiv.subtypePreimage (fun b => b ∈ Set.range f) η)
  constructor
  · intro h
    funext b
    exact (congrArg F (Set.apply_rangeSplitting f b).symm).trans (h _)
  · intro h a
    exact (congrFun h (Set.rangeFactorization f a)).trans (hη a)

theorem card_function_extensions [Finite B] (f : A → B) (ξ : A → C)
    (hξ : ξ.FactorsThrough f) :
    Nat.card {F : B → C // ∀ a, F (f a) = ξ a} =
      Nat.card C ^ (Nat.card B - Nat.card (Set.range f)) := by
  rw [Nat.card_congr (functionExtensionsEquiv f ξ hξ), Nat.card_fun]
  congr 1
  let : Fintype B := Fintype.ofFinite _
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

/-- The number of component classes met by the observations. -/
def observedClassCount (R : Setoid V) (v : A → V) : ℕ :=
  Nat.card (Quotient (R.comap v))

theorem observedClassCount_eq_range (R : Setoid V) (v : A → V) :
    observedClassCount R v = Nat.card (Set.range (Quotient.mk R ∘ v)) :=
  Nat.card_congr (Setoid.comapQuotientEquiv v R)

theorem observedClassCount_le [Finite V] (R : Setoid V) (v : A → V) :
    observedClassCount R v ≤ Nat.card (Quotient R) := by
  rw [observedClassCount_eq_range]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- A consistent observed pattern extends to one colour choice on each
unobserved component. -/
theorem card_clusterColoring_cylinder_of_compatible [Finite V]
    (R : Setoid V) (v : A → V) (ξ : A → C) (hξ : R.comap v ≤ Setoid.ker ξ) :
    Nat.card {σ : ClusterColoring R C // ∀ a, σ.val (v a) = ξ a} =
      Nat.card C ^ (Nat.card (Quotient R) - observedClassCount R v) := by
  let f : A → Quotient R := Quotient.mk R ∘ v
  have hf : ξ.FactorsThrough f := by
    intro a b h
    have hr : R.r (v a) (v b) := Quotient.exact h
    exact hξ hr
  let e := (clusterColoringEquiv R (C := C)).subtypeEquiv
    (p := fun σ => ∀ a, σ.val (v a) = ξ a)
    (q := fun F => ∀ a, F (f a) = ξ a) (fun _ => Iff.rfl)
  rw [Nat.card_congr e, card_function_extensions f ξ hf, observedClassCount_eq_range]

/-- Exact extension count, including inconsistent patterns. -/
theorem card_clusterColoring_cylinder [Finite V]
    (R : Setoid V) (v : A → V) (ξ : A → C) :
    Nat.card {σ : ClusterColoring R C // ∀ a, σ.val (v a) = ξ a} =
      if R.comap v ≤ Setoid.ker ξ then
        Nat.card C ^ (Nat.card (Quotient R) - observedClassCount R v) else 0 := by
  by_cases hξ : R.comap v ≤ Setoid.ker ξ
  · rw [ite_eq_left hξ, card_clusterColoring_cylinder_of_compatible R v ξ hξ]
  · rw [ite_eq_right hξ]
    let : IsEmpty {σ : ClusterColoring R C // ∀ a, σ.val (v a) = ξ a} :=
      ⟨fun σ => hξ (fun a b hab =>
        (σ.property a).symm.trans ((σ.val.property hab).trans (σ.property b)))⟩
    exact Nat.card_of_isEmpty

theorem card_compatible_cylinder [Finite V]
    (R : Setoid V) (v : A → V) (ξ : A → C) :
    Nat.card {σ : V → C // R ≤ Setoid.ker σ ∧ ∀ a, σ (v a) = ξ a} =
      if R.comap v ≤ Setoid.ker ξ then
        Nat.card C ^ (Nat.card (Quotient R) - observedClassCount R v) else 0 := by
  rw [← card_clusterColoring_cylinder R v ξ]
  exact (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun σ : V → C => R ≤ Setoid.ker σ) (fun σ => ∀ a, σ (v a) = ξ a))).symm

/-- The finite-pattern kernel determined solely by the observed connection
partition and its prescribed colours. -/
def clusterCylinderProbability (R : Setoid V) (v : A → V) (ξ : A → C) : ℝ :=
  if R.comap v ≤ Setoid.ker ξ then
    ((Nat.card C : ℝ) ^ observedClassCount R v)⁻¹ else 0

/-- Exact free cylinder probability under independent uniform component colours. -/
theorem clusterColoringProbability_cylinder [Fintype V] [Fintype C] [Nonempty C]
    (R : Setoid V) (v : A → V) (ξ : A → C) :
    (∑ σ : V → C, if ∀ a, σ (v a) = ξ a then clusterColoringProbability R σ else 0) =
      clusterCylinderProbability R v ξ := by
  have hc : (Nat.card C : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := C)).ne'
  have ht (σ : V → C) :
      (if ∀ a, σ (v a) = ξ a then clusterColoringProbability R σ else 0) =
      if R ≤ Setoid.ker σ ∧ ∀ a, σ (v a) = ξ a then
        ((Nat.card C : ℝ) ^ Nat.card (Quotient R))⁻¹ else 0 := by
    unfold clusterColoringProbability
    by_cases hR : R ≤ Setoid.ker σ <;>
      by_cases hσ : ∀ a, σ (v a) = ξ a <;> simp [hR, hσ]
  simp only [ht, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    card_compatible_cylinder, clusterCylinderProbability]
  by_cases hξ : R.comap v ≤ Setoid.ker ξ
  · simp only [hξ, ↓reduceIte, Nat.cast_pow]
    rw [pow_sub₀ _ hc (observedClassCount_le R v), mul_right_comm,
      mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul]
  · simp only [hξ, ↓reduceIte, Nat.cast_zero, zero_mul]

/-- Add one distinguished observation or one distinguished prescribed colour. -/
def markedMap (f : A → B) (b : B) (a : Option A) : B := a.elim b f

theorem markedMap_agreement_iff (v : A → V) (g : V) (ξ : A → C) (i : C) (σ : V → C) :
    (∀ a, σ (markedMap v g a) = markedMap ξ i a) ↔
      σ g = i ∧ ∀ a, σ (v a) = ξ a := by
  simp only [Option.forall, markedMap, Option.elim_none, Option.elim_some]

theorem observedClassCount_marked_pos [Finite V] (R : Setoid V) (v : A → V) (g : V) :
    0 < observedClassCount R (markedMap v g) := by
  rw [observedClassCount_eq_range]
  let : Nonempty (Set.range (Quotient.mk R ∘ markedMap v g)) :=
    ⟨⟨Quotient.mk R g, none, rfl⟩⟩
  exact Nat.card_pos

/-- Pinning and observing are a single pattern on the marked observation set. -/
def pinnedCylinderEquiv (R : Setoid V) (v : A → V) (ξ : A → C) (g : V) (i : C) :
    {σ : PinnedClusterColoring R g i // ∀ a, σ.val.val (v a) = ξ a} ≃
      {σ : ClusterColoring R C // ∀ a, σ.val (markedMap v g a) = markedMap ξ i a} where
  toFun σ := ⟨σ.val.val, (markedMap_agreement_iff v g ξ i σ.val.val.val).mpr
    ⟨σ.val.property, σ.property⟩⟩
  invFun σ := ⟨⟨σ.val, ((markedMap_agreement_iff v g ξ i σ.val.val).mp σ.property).1⟩,
    ((markedMap_agreement_iff v g ξ i σ.val.val).mp σ.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact count of pinned component colourings realizing an observed pattern. -/
theorem card_pinnedClusterColoring_cylinder [Finite V]
    (R : Setoid V) (v : A → V) (ξ : A → C) (g : V) (i : C) :
    Nat.card {σ : PinnedClusterColoring R g i // ∀ a, σ.val.val (v a) = ξ a} =
      if R.comap (markedMap v g) ≤ Setoid.ker (markedMap ξ i) then
        Nat.card C ^ (Nat.card (Quotient R) - observedClassCount R (markedMap v g)) else 0 := by
  rw [Nat.card_congr (pinnedCylinderEquiv R v ξ g i), card_clusterColoring_cylinder]

/-- The pinned cylinder kernel counts only observed classes other than the
distinguished class, and enforces the colour prescribed on that class. -/
def pinnedClusterCylinderProbability (R : Setoid V) (v : A → V) (ξ : A → C)
    (g : V) (i : C) : ℝ :=
  if R.comap (markedMap v g) ≤ Setoid.ker (markedMap ξ i) then
    ((Nat.card C : ℝ) ^ (observedClassCount R (markedMap v g) - 1))⁻¹ else 0

end

end PottsDiscontinuity.Potts
