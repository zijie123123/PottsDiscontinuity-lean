module

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-!
# Adjacent transpositions in the coordinate Bethe amplitudes

Companion paper, Lemma `lem:ratios`, equation (8). Products are over ordered index pairs.
The finite product argument explicitly isolates the single pair whose order is reversed
by an adjacent transposition.
-/

@[expose] public section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

private theorem adjacent_swap_lt {n : ℕ} {a b i j : Fin n}
    (hab : a.val + 1 = b.val) (hij : i < j) (hne : (i, j) ≠ (a, b)) :
    Equiv.swap a b i < Equiv.swap a b j := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all only <;> first | contradiction | omega

/-- An adjacent transposition changes exactly one factor in a product over `i < j`.
The multiplication form avoids dividing by factors that might vanish. -/
theorem pair_product_adjacent_swap {n : ℕ} (f : Fin n → Fin n → ℂ)
    {a b : Fin n} (hab : a.val + 1 = b.val) :
    (∏ i, ∏ j ∈ Ioi i, f (Equiv.swap a b i) (Equiv.swap a b j)) * f a b =
      (∏ i, ∏ j ∈ Ioi i, f i j) * f b a := by
  classical
  let D : Finset (Fin n × Fin n) := (univ ×ˢ univ).filter (fun q => q.1 < q.2)
  let s := Equiv.swap a b
  have hablt : a < b := by omega
  have hmem : (a, b) ∈ D := by simp [D, hablt]
  have hstable : ∀ q ∈ D.erase (a, b), (s q.1, s q.2) ∈ D.erase (a, b) := by
    intro q hq
    obtain ⟨hne, hq⟩ := mem_erase.mp hq
    have hlt : q.1 < q.2 := (mem_filter.mp hq).2
    apply mem_erase.mpr
    constructor
    · intro he
      have h1 := congrArg (fun r : Fin n × Fin n => s r.1) he
      have h2 := congrArg (fun r : Fin n × Fin n => s r.2) he
      have hq1 : q.1 = b := by simpa [s] using h1
      have hq2 : q.2 = a := by simpa [s] using h2
      rw [hq1, hq2] at hlt
      exact (not_lt_of_ge hablt.le) hlt
    · simp only [D, mem_filter, mem_product, mem_univ, and_self, true_and]
      exact adjacent_swap_lt hab hlt hne
  have hr : (∏ q ∈ D.erase (a, b), f (s q.1) (s q.2)) =
      ∏ q ∈ D.erase (a, b), f q.1 q.2 := by
    apply Finset.prod_bij (fun q _ => (s q.1, s q.2))
    · exact hstable
    · intro q _ r _ he
      exact Prod.ext (s.injective (congrArg Prod.fst he)) (s.injective (congrArg Prod.snd he))
    · intro q hq
      refine ⟨(s q.1, s q.2), hstable q hq, ?_⟩
      simp [s]
    · intro q _
      rfl
  have hpair : ∀ g : Fin n → Fin n → ℂ,
      (∏ i, ∏ j ∈ Ioi i, g i j) = ∏ q ∈ D, g q.1 q.2 := by
    intro g
    simp only [D, Finset.prod_filter, Finset.prod_product]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  rw [hpair, hpair]
  rw [← Finset.mul_prod_erase D (fun q => f (s q.1) (s q.2)) hmem,
    ← Finset.mul_prod_erase D (fun q => f q.1 q.2) hmem]
  change (f (s a) (s b) * _) * f a b = (f a b * _) * f b a
  simp only [s, Equiv.swap_apply_left, Equiv.swap_apply_right] at hr ⊢
  rw [hr]
  ring

/-- The adjacent amplitude relation, in multiplication form. Bethe equations are not needed.
Permutation multiplication is composition: `(σ * swap a b) i = σ (swap a b i)`. -/
theorem amplitude_adjacent_swap {n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) {a b : Fin n}
    (hab : a.val + 1 = b.val) :
    amplitude Δ p (σ * Equiv.swap a b) =
      -Complex.exp (I * (Bethe.theta Δ (p (σ a)) (p (σ b)) : ℂ)) * amplitude Δ p σ := by
  let f : Fin n → Fin n → ℂ := fun i j =>
    z (p (σ i)) * scattering Δ (p (σ i)) (p (σ j))
  have hf : f a b ≠ 0 := mul_ne_zero (z_ne_zero _) (scattering_ne_zero hΔ _ _)
  have hp := pair_product_adjacent_swap f hab
  have habne : a ≠ b := by omega
  have hsign : (((Equiv.Perm.sign (σ * Equiv.swap a b) : ℤ) : ℂ)) =
      -(((Equiv.Perm.sign σ : ℤ) : ℂ)) := by
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap habne]
  have he : Complex.exp (I * (Bethe.theta Δ (p (σ a)) (p (σ b)) : ℂ)) =
      f b a / f a b := exp_I_theta_eq_scattering hΔ _ _
  have hm : amplitude Δ p (σ * Equiv.swap a b) * f a b =
      -(amplitude Δ p σ * f b a) := by
    unfold amplitude
    rw [hsign]
    change (-(((Equiv.Perm.sign σ : ℤ) : ℂ)) *
      (∏ i, ∏ j ∈ Ioi i, f (Equiv.swap a b i) (Equiv.swap a b j))) * f a b =
      -((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (∏ i, ∏ j ∈ Ioi i, f i j) * f b a)
    linear_combination -(((Equiv.Perm.sign σ : ℤ) : ℂ)) * hp
  apply mul_right_cancel₀ hf
  rw [he]
  calc
    amplitude Δ p (σ * Equiv.swap a b) * f a b = -(amplitude Δ p σ * f b a) := hm
    _ = (-(f b a / f a b) * amplitude Δ p σ) * f a b := by field_simp

end PottsDiscontinuity.BetheAnsatz
