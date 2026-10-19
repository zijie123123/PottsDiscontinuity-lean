module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.GraphCoupling

/-! One-point pinned and two-point free colouring kernels, with the corrected factors. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical
noncomputable section

private theorem setoid_top_of_two_classes {A : Type*} (R : Setoid A) (x y : A)
    (hcover : ∀ a, a = x ∨ a = y) (hxy : R x y) : R = ⊤ := by
  apply top_unique
  intro a b _
  rcases hcover a with rfl | rfl <;> rcases hcover b with rfl | rfl
  · exact R.refl _
  · exact hxy
  · exact R.symm hxy
  · exact R.refl _

private theorem setoid_bot_of_two_classes {A : Type*} (R : Setoid A) (x y : A)
    (hcover : ∀ a, a = x ∨ a = y) (hxy : ¬ R x y) : R = ⊥ := by
  apply bot_unique
  intro a b hab
  rcases hcover a with rfl | rfl <;> rcases hcover b with rfl | rfl
  · rfl
  · exact (hxy hab).elim
  · exact (hxy (R.symm hab)).elim
  · rfl

private theorem card_quotient_top {A : Type*} [Nonempty A] : Nat.card (Quotient (⊤ : Setoid A)) = 1 := by
  let : Subsingleton (Quotient (⊤ : Setoid A)) := Quotient.subsingleton_iff.mpr rfl
  let : Nonempty (Quotient (⊤ : Setoid A)) := ⟨Quotient.mk _ (Classical.choice (inferInstance : Nonempty A))⟩
  exact Nat.card_unique

/-- Two observed spins have one uniform colour if connected, and two independent
uniform colours otherwise. -/
theorem free_two_point_kernel (q : ℕ) (c : Set.Icc 1 q) (R : Setoid Bool) :
    clusterCylinderProbability R id (fun _ : Bool => c) =
      if R false true then (q : ℝ)⁻¹ else ((q : ℝ) ^ 2)⁻¹ := by
  have hcomp : R.comap id ≤ Setoid.ker (fun _ : Bool => c) := by intro _ _ _; rfl
  unfold clusterCylinderProbability
  rw [ite_eq_left hcomp, card_pottsColors]
  have hcount : observedClassCount R id = Nat.card (Quotient R) := rfl
  rw [hcount]
  have hcover : ∀ b : Bool, b = false ∨ b = true := by intro b; cases b <;> simp
  by_cases h : R false true
  · rw [ite_eq_left h, setoid_top_of_two_classes R false true hcover h, card_quotient_top, pow_one]
  · rw [ite_eq_right h, setoid_bot_of_two_classes R false true hcover h,
      Nat.card_congr (Setoid.quotientBotEquiv : Quotient (⊥ : Setoid Bool) ≃ Bool)]
    norm_num [Nat.card_eq_fintype_card]

/-- An observed spin equals the pinned colour certainly in the ghost class,
and with uniform probability otherwise. -/
theorem wired_one_point_kernel (q : ℕ) (c : Set.Icc 1 q) (R : Setoid (Option PUnit)) :
    pinnedClusterCylinderProbability R some (fun _ : PUnit => c) none c =
      if R (some PUnit.unit) none then 1 else (q : ℝ)⁻¹ := by
  have hcomp : R.comap (markedMap some none) ≤ Setoid.ker (markedMap (fun _ : PUnit => c) c) := by
    intro a b _
    cases a <;> cases b <;> rfl
  unfold pinnedClusterCylinderProbability
  rw [ite_eq_left hcomp, card_pottsColors]
  have hid : markedMap some none = (id : Option PUnit → Option PUnit) := by
    funext a; cases a <;> rfl
  have hcount : observedClassCount R (markedMap some none) = Nat.card (Quotient R) := by
    rw [hid]
    rfl
  rw [hcount]
  have hcover : ∀ a : Option PUnit, a = some PUnit.unit ∨ a = none := by
    intro a; cases a with
    | none => simp
    | some a => cases a; simp
  by_cases h : R (some PUnit.unit) none
  · rw [ite_eq_left h, setoid_top_of_two_classes R _ _ hcover h, card_quotient_top]
    norm_num
  · rw [ite_eq_right h, setoid_bot_of_two_classes R _ _ hcover h,
      Nat.card_congr (Setoid.quotientBotEquiv : Quotient (⊥ : Setoid (Option PUnit)) ≃ Option PUnit)]
    norm_num

end
end PottsDiscontinuity.Potts
