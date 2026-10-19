module

public import PottsDiscontinuity.SixVertex.Defs

/-!
# Interlacing via counting functions

The interlacing relation `x_1 ≤ y_1 ≤ x_2 ≤ ⋯ ≤ x_n ≤ y_n` of (1.5) is equivalent to the pointwise
inequalities `cnt y t ≤ cnt x t ≤ cnt y t + 1` between the counting functions
`cnt x t = |{a ∈ x : a ≤ t}|` (and the equality of cardinalities).
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

/-- `cnt x t = |{a ∈ x : a ≤ t}|`: the number of entries of `x` that are `≤ t`. -/
def cnt (x : Finset (Fin N)) (t : Fin N) : ℕ := (x.filter (· ≤ t)).card

/-- The `k`-th smallest entry of `x` is `≤ t` iff `x` has more than `k` entries `≤ t`. -/
theorem orderEmbOfFin_le_iff {x : Finset (Fin N)} {n : ℕ} (h : x.card = n) (k : Fin n)
    (t : Fin N) : x.orderEmbOfFin h k ≤ t ↔ k.val < cnt x t := by
  constructor
  · intro hk
    have hsub : (Finset.Iic k).image (x.orderEmbOfFin h) ⊆ x.filter (· ≤ t) := by
      intro a ha
      obtain ⟨m, hm, rfl⟩ := mem_image.1 ha
      rw [mem_filter]
      exact ⟨x.orderEmbOfFin_mem h m, le_trans ((x.orderEmbOfFin h).monotone (mem_Iic.1 hm)) hk⟩
    have := card_le_card hsub
    rw [card_image_of_injective _ (x.orderEmbOfFin h).injective, Fin.card_Iic] at this
    unfold cnt
    omega
  · intro hk
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hsub : x.filter (· ≤ t) ⊆ (Finset.Iio k).image (x.orderEmbOfFin h) := by
      intro a ha
      rw [mem_filter] at ha
      have : a ∈ Set.range (x.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]; exact ha.1
      obtain ⟨m, rfl⟩ := this
      refine mem_image.2 ⟨m, mem_Iio.2 ?_, rfl⟩
      exact (x.orderEmbOfFin h).lt_iff_lt.1 (lt_of_le_of_lt ha.2 hlt)
    have := card_le_card hsub
    have h2 : ((Finset.Iio k).image (x.orderEmbOfFin h)).card ≤ (Finset.Iio k).card :=
      card_image_le
    rw [Fin.card_Iio] at h2
    unfold cnt at hk
    omega

theorem cnt_le_card (x : Finset (Fin N)) (t : Fin N) : cnt x t ≤ x.card :=
  card_le_card (filter_subset _ _)

/-- Counting-function characterisation of `x_1 ≤ y_1 ≤ x_2 ≤ ⋯ ≤ x_n ≤ y_n`. -/
theorem interlacedLE_iff (x y : Finset (Fin N)) :
    InterlacedLE x y ↔ x.card = y.card ∧ ∀ t, cnt y t ≤ cnt x t ∧ cnt x t ≤ cnt y t + 1 := by
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨h, fun t => ⟨?_, ?_⟩⟩
    · by_contra hlt
      replace hlt := not_le.1 hlt
      have hm : cnt x t < x.card := lt_of_lt_of_le hlt (h ▸ cnt_le_card y t)
      have hy : y.orderEmbOfFin h.symm ⟨cnt x t, hm⟩ ≤ t :=
        (orderEmbOfFin_le_iff h.symm _ t).2 hlt
      have hx : x.orderEmbOfFin rfl ⟨cnt x t, hm⟩ ≤ t := le_trans (h1 _) hy
      have := (orderEmbOfFin_le_iff rfl _ t).1 hx
      simp at this
    · by_contra hlt
      replace hlt := not_le.1 hlt
      have hm : cnt y t + 1 < x.card := lt_of_lt_of_le hlt (cnt_le_card x t)
      have hk : cnt y t < x.card := by omega
      have hx : x.orderEmbOfFin rfl ⟨cnt y t + 1, hm⟩ ≤ t :=
        (orderEmbOfFin_le_iff rfl _ t).2 hlt
      have hy : y.orderEmbOfFin h.symm ⟨cnt y t, hk⟩ ≤ t :=
        le_trans (h2 ⟨cnt y t, hk⟩ ⟨cnt y t + 1, hm⟩ rfl) hx
      have := (orderEmbOfFin_le_iff h.symm _ t).1 hy
      simp at this
  · rintro ⟨h, hc⟩
    refine ⟨h, fun k => ?_, fun k l hkl => ?_⟩
    · set t := y.orderEmbOfFin h.symm k with ht
      have h1 : k.val < cnt y t := (orderEmbOfFin_le_iff h.symm k t).1 le_rfl
      exact (orderEmbOfFin_le_iff rfl k t).2 (lt_of_lt_of_le h1 (hc t).1)
    · set t := x.orderEmbOfFin rfl l with ht
      have h1 : l.val < cnt x t := (orderEmbOfFin_le_iff rfl l t).1 le_rfl
      refine (orderEmbOfFin_le_iff h.symm k t).2 ?_
      have := (hc t).2
      omega

/-- Counting-function characterisation of the interlacing relation of (1.5). -/
theorem interlaced_iff (x y : Finset (Fin N)) :
    Interlaced x y ↔ x.card = y.card ∧
      ((∀ t, cnt y t ≤ cnt x t ∧ cnt x t ≤ cnt y t + 1) ∨
        ∀ t, cnt x t ≤ cnt y t ∧ cnt y t ≤ cnt x t + 1) := by
  unfold Interlaced
  rw [interlacedLE_iff, interlacedLE_iff]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact ⟨h, Or.inl h'⟩
    · exact ⟨h.symm, Or.inr h'⟩
  · rintro ⟨h, h' | h'⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h.symm, h'⟩

theorem Interlaced.symm {x y : Finset (Fin N)} (h : Interlaced x y) : Interlaced y x :=
  Or.symm h

theorem interlaced_comm (x y : Finset (Fin N)) : Interlaced x y ↔ Interlaced y x :=
  ⟨Interlaced.symm, Interlaced.symm⟩

theorem Interlaced.card_eq {x y : Finset (Fin N)} (h : Interlaced x y) : x.card = y.card :=
  ((interlaced_iff x y).1 h).1

theorem interlaced_refl (x : Finset (Fin N)) : Interlaced x x :=
  Or.inl ((interlacedLE_iff x x).2 ⟨rfl, fun _ => ⟨le_rfl, Nat.le_succ _⟩⟩)

end PottsDiscontinuity.SixVertex
