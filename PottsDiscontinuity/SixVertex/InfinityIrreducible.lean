module

public import PottsDiscontinuity.SixVertex.InfinityDescent

/-!
# Irreducibility on independent row states

A connected component has a minimum of the sum of occupied positions. Such a
minimum contains zero and is closed under subtracting two. It is consequently an
even initial segment. Equal particle counts make all component minima identical.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

abbrev Reach (x y : IndependentState N n) : Prop :=
  Relation.ReflTransGen (fun a b => 0 < infinityRestriction N n a b) x y

private theorem reach_symm {x y : IndependentState N n} (h : Reach x y) : Reach y x :=
  reflTransGen_symm_of_symm (fun a b h => by rwa [infinityRestriction_symm]) h

private theorem minimum_contains_zero (hn : 0 < n) (p : IndependentState N n)
    (hmin : ∀ y, Reach p y → positionSum p.1.1 ≤ positionSum y.1.1) :
    ∀ z : Fin N, z.val = 0 → z ∈ p.1.1 := by
  intro z hz
  by_contra hnot
  have h0 : ∀ i ∈ p.1.1, 0 < i.val := by
    intro i hi
    by_contra hzero
    have he : i = z := Fin.ext (by omega)
    exact hnot (he ▸ hi)
  have hne : p.1.1.Nonempty := card_pos.mp (by rw [p.1.2]; exact hn)
  have hlt := positionSum_rotateDown_lt p.1.1 hne h0
  have hle := hmin (unrotateIndependent p) (unrotateIndependent_reachable hn p)
  exact (not_lt_of_ge hle) hlt

private theorem minimum_closed_two (hn : 0 < n) (p : IndependentState N n)
    (hmin : ∀ y, Reach p y → positionSum p.1.1 ≤ positionSum y.1.1) :
    ∀ i ∈ p.1.1, ∀ j : Fin N, 2 ≤ i.val → j.val + 2 = i.val → j ∈ p.1.1 := by
  intro i hi j hi2 hji2
  by_contra hj
  let k : Fin N := ⟨i.val - 1, by omega⟩
  have hki : nxt k = i := by
    apply Fin.ext
    rw [nxt_val_of_lt k (by dsimp [k]; omega)]
    dsimp [k]
    omega
  have hkj : prv k = j := by
    apply Fin.ext
    rw [prv_val_of_pos k (by dsimp [k]; omega)]
    dsimp [k]
    omega
  have hk : k ∉ p.1.1 := fun h => p.2 k h (hki ▸ hi)
  obtain ⟨q, hq, hpq⟩ := infinityRestriction_slide_left_reachable hn p hi hk
    (by rwa [hkj]) hki
  have hle := hmin q hpq
  have hlt := positionSum_jump_lt hi hk (show k.val < i.val by dsimp [k]; omega)
  rw [← hq] at hlt
  exact (not_lt_of_ge hle) hlt

private theorem minimum_unique (hn : 0 < n) (p q : IndependentState N n)
    (hp : ∀ y, Reach p y → positionSum p.1.1 ≤ positionSum y.1.1)
    (hq : ∀ y, Reach q y → positionSum q.1.1 ≤ positionSum y.1.1) : p = q := by
  have hpc := minimum_closed_two hn p hp
  have hqc := minimum_closed_two hn q hq
  have hpe := even_of_closed_two p.2 (minimum_contains_zero hn p hp) hpc
  have hqe := even_of_closed_two q.2 (minimum_contains_zero hn q hq) hqc
  apply Subtype.ext
  apply Subtype.ext
  exact eq_of_even_prefix (p.1.2.trans q.1.2.symm) hpe hqe
    (even_prefix_of_closed_two hpe hpc) (even_prefix_of_closed_two hqe hqc)

private theorem exists_component_minimum (x : IndependentState N n) :
    ∃ p, Reach x p ∧ ∀ y, Reach p y → positionSum p.1.1 ≤ positionSum y.1.1 := by
  classical
  let s : Set (IndependentState N n) := {p | Reach x p}
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image s (fun p => positionSum p.1.1)
    (Set.toFinite s) ⟨x, Relation.ReflTransGen.refl⟩
  exact ⟨p, hp, fun y hy => hmin y (hp.trans hy)⟩

/-- Any two independent states communicate through positive entries of the limiting matrix. -/
theorem infinityRestriction_reachable (hn : 0 < n) (x y : IndependentState N n) :
    Relation.ReflTransGen (fun a b : IndependentState N n =>
      0 < infinityRestriction N n a b) x y := by
  obtain ⟨p, hxp, hp⟩ := exists_component_minimum x
  obtain ⟨q, hyq, hq⟩ := exists_component_minimum y
  have he := minimum_unique hn p q hp hq
  rw [← he] at hyq
  exact hxp.trans (reach_symm hyq)

/-- A positive power (with strictly positive exponent) connects every independent pair. -/
theorem infinityRestriction_exists_pow_pos (hn : 0 < n) (x y : IndependentState N n) :
    ∃ k > 0, 0 < (infinityRestriction N n ^ k) x y := by
  obtain ⟨k, hk⟩ := exists_pow_pos_of_reflTransGen infinityRestriction_nonneg
    (infinityRestriction_reachable hn x y)
  by_cases hk0 : k = 0
  · subst k
    have hxy : x = y := by
      by_contra h
      simp only [pow_zero, Matrix.one_apply, h, ↓reduceIte, lt_self_iff_false] at hk
    subst y
    exact ⟨2, by norm_num, infinityRestriction_square_self_pos hn x⟩
  · exact ⟨k, Nat.pos_of_ne_zero hk0, hk⟩

/-- The restriction to configurations without consecutive up arrows is irreducible. -/
theorem infinityRestriction_isIrreducible (hn : 0 < n) :
    (infinityRestriction N n).IsIrreducible :=
  (Matrix.isIrreducible_iff_exists_pow_pos infinityRestriction_nonneg).mpr
    (infinityRestriction_exists_pow_pos hn)

end PottsDiscontinuity.SixVertex
