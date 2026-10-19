module

public import PottsDiscontinuity.Potts.GhostBoundary
public import PottsDiscontinuity.Potts.CylinderColoring

/-!
# Exact ghost cylinder formula for the frozen Potts law

The spin carrier remains the original finite vertex set. Extending by the
fixed ghost colour identifies its compatible cylinder patterns with the
marked component-colouring patterns. Consequently the finite Potts cylinder
formula uses only the connection partition of the observed vertices and ghost.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

local instance ghostCylinderLiteralBondDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (LiteralBond V) := fun _ _ => Classical.propDecidable _

local instance ghostCylinderBoundaryVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (BoundaryVertex V) := Fintype.ofFinite _

/-- The literal colouring correspondence preserves every observed spin. -/
def literalCylinderEquiv (q : ℕ) (V : Finset (ℤ × ℤ))
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool)
    {A : Type*} (v : A → ↥(V : Set (ℤ × ℤ))) (ξ : A → Set.Icc 1 q) :
    {σ : SpinConfiguration q V //
      (∀ e, ω e = true → literalAgreement q V i σ e) ∧ ∀ a, σ (v a) = ξ a} ≃
      {τ : PinnedClusterColoring (ghostOpenGraph V ω).reachableSetoid none (boundaryColor q i hi) //
        ∀ a, τ.val.val (some (v a)) = ξ a} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun σ : SpinConfiguration q V => ∀ e, ω e = true → literalAgreement q V i σ e)
    (fun σ => ∀ a, σ (v a) = ξ a)).symm.trans
      ((literalColoringEquiv q V i hi ω).subtypeEquiv
        (p := fun σ => ∀ a, σ.val (v a) = ξ a)
        (q := fun τ => ∀ a, τ.val.val (some (v a)) = ξ a) (fun _ => Iff.rfl))

/-- Number of original spin configurations realizing a compatible cylinder
under the literal ghost-bond constraints. -/
theorem card_literalAgreement_cylinder (q : ℕ) (V : Finset (ℤ × ℤ))
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool)
    {A : Type*} (v : A → ↥(V : Set (ℤ × ℤ))) (ξ : A → Set.Icc 1 q) :
    Nat.card {σ : SpinConfiguration q V //
      (∀ e, ω e = true → literalAgreement q V i σ e) ∧ ∀ a, σ (v a) = ξ a} =
      if (ghostOpenGraph V ω).reachableSetoid.comap (markedMap (some ∘ v) none) ≤
          Setoid.ker (markedMap ξ (boundaryColor q i hi)) then
        q ^ (ghostComponentCount V ω -
          observedClassCount (ghostOpenGraph V ω).reachableSetoid (markedMap (some ∘ v) none))
      else 0 := by
  rw [Nat.card_congr (literalCylinderEquiv q V i hi ω v ξ),
    card_pinnedClusterColoring_cylinder, card_pottsColors]
  rfl

/-- The original-spin cylinder mass under uniform ghost-pinned component
colours depends only on the marked connection partition. -/
theorem ghostColoringProbability_cylinder (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool)
    {A : Type*} (v : A → ↥(V : Set (ℤ × ℤ))) (ξ : A → Set.Icc 1 q) :
    (∑ σ : SpinConfiguration q V,
      if ∀ a, σ (v a) = ξ a then ghostColoringProbability q V i hi ω σ else 0) =
      pinnedClusterCylinderProbability (ghostOpenGraph V ω).reachableSetoid
        (some ∘ v) ξ none (boundaryColor q i hi) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have ht (σ : SpinConfiguration q V) :
      (if ∀ a, σ (v a) = ξ a then ghostColoringProbability q V i hi ω σ else 0) =
      if (∀ e, ω e = true → literalAgreement q V i σ e) ∧ ∀ a, σ (v a) = ξ a then
        ((q : ℝ) ^ (ghostComponentCount V ω - 1))⁻¹ else 0 := by
    unfold ghostColoringProbability
    simp only [← literalAgreement_iff_ghost q V i hi]
    by_cases ho : ∀ a, σ (v a) = ξ a <;> simp [ho]
  simp only [ht, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    card_literalAgreement_cylinder q V i hi ω v ξ, pinnedClusterCylinderProbability, card_pottsColors]
  by_cases hξ : (ghostOpenGraph V ω).reachableSetoid.comap (markedMap (some ∘ v) none) ≤
      Setoid.ker (markedMap ξ (boundaryColor q i hi))
  · simp only [hξ, ↓reduceIte, Nat.cast_pow]
    have hm := observedClassCount_marked_pos (ghostOpenGraph V ω).reachableSetoid (some ∘ v) none
    have hmk : observedClassCount (ghostOpenGraph V ω).reachableSetoid
        (markedMap (some ∘ v) none) ≤ ghostComponentCount V ω :=
      observedClassCount_le (ghostOpenGraph V ω).reachableSetoid (markedMap (some ∘ v) none)
    have he : ghostComponentCount V ω -
          observedClassCount (ghostOpenGraph V ω).reachableSetoid (markedMap (some ∘ v) none) =
        (ghostComponentCount V ω - 1) -
          (observedClassCount (ghostOpenGraph V ω).reachableSetoid (markedMap (some ∘ v) none) - 1) := by
      omega
    rw [he, pow_sub₀ _ hq0 (Nat.sub_le_sub_right hmk 1), mul_right_comm,
      mul_inv_cancel₀ (pow_ne_zero _ hq0), one_mul]
  · simp only [hξ, ↓reduceIte, Nat.cast_zero, zero_mul]

/-- Exact cylinder formula for the frozen finite Potts law with its literal
one-field-term-per-boundary-vertex Hamiltonian and positive boundary colour. -/
theorem pottsProb_ghost_cylinder (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    {A : Type*} (v : A → ↥(V : Set (ℤ × ℤ))) (ξ : A → Set.Icc 1 q) :
    (∑ σ : SpinConfiguration q V,
      if ∀ a, σ (v a) = ξ a then pottsProb q V β i σ else 0) =
      ∑ ω : LiteralBond V → Bool, ghostRCProbability q V β ω *
        pinnedClusterCylinderProbability (ghostOpenGraph V ω).reachableSetoid
          (some ∘ v) ξ none (boundaryColor q i hi) := by
  have h := pottsProb_event_eq_ghostMixture q hq V β i hi {σ | ∀ a, σ (v a) = ξ a}
  simpa only [Set.mem_ofPred_eq, ghostColoringProbability_cylinder q hq V i hi] using h

end

end PottsDiscontinuity.Potts
