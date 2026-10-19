module

public import PottsDiscontinuity.SixVertex.InfinityMoves

/-! # Finite descent for independent row states -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

/-- The ordinary sum of occupied positions, used only as a finite descent function. -/
def positionSum (x : Finset (Fin N)) : ℕ := ∑ i ∈ x, i.val

theorem nxt_val_of_lt (i : Fin N) (hi : i.val + 1 < N) : (nxt i).val = i.val + 1 := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ k =>
    exact congrArg Fin.val (finRotate_of_lt (show i.val < k by omega))

theorem prv_val_of_pos (i : Fin N) (hi : 0 < i.val) : (prv i).val = i.val - 1 := by
  let j : Fin N := ⟨i.val - 1, by omega⟩
  have hj : nxt j = i := by
    apply Fin.ext
    rw [nxt_val_of_lt j (by dsimp [j]; omega)]
    dsimp [j]
    omega
  have he : prv i = j := by
    rw [← hj]
    exact (finRotate N).symm_apply_apply j
  rw [he]

/-- Rotation one site to the left. -/
def rotateDown (x : Finset (Fin N)) : Finset (Fin N) := x.image prv

@[simp] theorem mem_rotateDown (x : Finset (Fin N)) (i : Fin N) :
    i ∈ rotateDown x ↔ nxt i ∈ x := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    simpa only [prv, nxt, Equiv.apply_symm_apply] using hj
  · intro hi
    exact mem_image.mpr ⟨nxt i, hi, (finRotate N).symm_apply_apply i⟩

theorem NoConsecutiveUp.rotateDown {x : Finset (Fin N)} (hx : NoConsecutiveUp x) :
    NoConsecutiveUp (rotateDown x) := by
  intro i hi hni
  rw [mem_rotateDown] at hi hni
  exact hx (nxt i) hi hni

def unrotateIndependent (x : IndependentState N n) : IndependentState N n :=
  ⟨⟨rotateDown x.1.1, (card_image_of_injective _ (finRotate N).symm.injective).trans x.1.2⟩,
    x.2.rotateDown⟩

@[simp] theorem rotateIndependent_unrotate (x : IndependentState N n) :
    rotateIndependent (unrotateIndependent x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  simp only [rotateIndependent, unrotateIndependent, mem_rotateUp, mem_rotateDown,
    nxt, prv, Equiv.apply_symm_apply]

theorem unrotateIndependent_reachable (hn : 0 < n) (x : IndependentState N n) :
    Relation.ReflTransGen (fun a b : IndependentState N n =>
      0 < infinityRestriction N n a b) x (unrotateIndependent x) := by
  apply Relation.ReflTransGen.single
  rw [infinityRestriction_symm]
  have he := infinityRestriction_rotate hn (unrotateIndependent x)
  rw [rotateIndependent_unrotate] at he
  rw [he]
  norm_num

/-- If the row does not contain zero, moving every particle left strictly lowers the sum. -/
theorem positionSum_rotateDown_lt (x : Finset (Fin N)) (hne : x.Nonempty)
    (h0 : ∀ i ∈ x, 0 < i.val) : positionSum (rotateDown x) < positionSum x := by
  unfold positionSum rotateDown
  rw [sum_image (fun i _ j _ he => (finRotate N).symm.injective he)]
  apply sum_lt_sum
  · intro i hi
    rw [prv_val_of_pos i (h0 i hi)]
    omega
  · obtain ⟨i, hi⟩ := hne
    refine ⟨i, hi, ?_⟩
    rw [prv_val_of_pos i (h0 i hi)]
    exact Nat.sub_lt (h0 i hi) (by omega)

/-- Moving one particle to a strictly smaller vacant coordinate lowers the sum. -/
theorem positionSum_jump_lt {x : Finset (Fin N)} {i j : Fin N}
    (hi : i ∈ x) (hj : j ∉ x) (hji : j.val < i.val) :
    positionSum (jump x i j) < positionSum x := by
  unfold positionSum jump
  rw [sum_insert (fun h => hj (mem_of_mem_erase h))]
  have he := sum_erase_add x (fun a : Fin N => a.val) hi
  omega

/-- A row closed under subtracting two and containing zero consists of even positions. -/
theorem even_of_closed_two {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (h0 : ∀ i : Fin N, i.val = 0 → i ∈ x)
    (hc : ∀ i ∈ x, ∀ j : Fin N, 2 ≤ i.val → j.val + 2 = i.val → j ∈ x) :
    ∀ i ∈ x, i.val % 2 = 0 := by
  have hall : ∀ k : ℕ, ∀ i : Fin N, i.val = k → i ∈ x → k % 2 = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik hi
      by_cases hk0 : k = 0
      · simp [hk0]
      by_cases hk1 : k = 1
      · let z : Fin N := ⟨0, by omega⟩
        have hz := h0 z rfl
        have hnz : nxt z = i := by
          apply Fin.ext
          rw [nxt_val_of_lt z (by dsimp [z]; omega)]
          dsimp [z]
          omega
        exact (hx z hz (hnz ▸ hi)).elim
      · let j : Fin N := ⟨k - 2, by omega⟩
        have hj := hc i hi j (by omega) (by dsimp [j]; omega)
        have he := ih (k - 2) (by omega) j rfl hj
        omega
  intro i hi
  exact hall i.val i rfl hi

/-- Closure by two also gives every smaller even coordinate below an occupied coordinate. -/
theorem even_prefix_of_closed_two {x : Finset (Fin N)}
    (he : ∀ i ∈ x, i.val % 2 = 0)
    (hc : ∀ i ∈ x, ∀ j : Fin N, 2 ≤ i.val → j.val + 2 = i.val → j ∈ x) :
    ∀ i ∈ x, ∀ j : Fin N, j.val ≤ i.val → j.val % 2 = 0 → j ∈ x := by
  have hall : ∀ k : ℕ, ∀ i : Fin N, i.val = k → i ∈ x →
      ∀ j : Fin N, j.val ≤ k → j.val % 2 = 0 → j ∈ x := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik hi j hj hje
      by_cases hji : j = i
      · exact hji ▸ hi
      have hei := he i hi
      have hjlt : j.val < k := by
        have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
        omega
      let l : Fin N := ⟨k - 2, by omega⟩
      have hl := hc i hi l (by omega) (by dsimp [l]; omega)
      apply ih (k - 2) (by omega) l rfl hl j (by omega) hje
  intro i hi j hj hje
  exact hall i.val i rfl hi j hj hje

/-- Two even initial segments of equal cardinality are identical. -/
theorem eq_of_even_prefix {x y : Finset (Fin N)} (hcard : x.card = y.card)
    (hex : ∀ i ∈ x, i.val % 2 = 0) (hey : ∀ i ∈ y, i.val % 2 = 0)
    (hpx : ∀ i ∈ x, ∀ j : Fin N, j.val ≤ i.val → j.val % 2 = 0 → j ∈ x)
    (hpy : ∀ i ∈ y, ∀ j : Fin N, j.val ≤ i.val → j.val % 2 = 0 → j ∈ y) : x = y := by
  by_cases hsub : x ⊆ y
  · exact eq_of_subset_of_card_le hsub hcard.ge
  · obtain ⟨i, hi, hiy⟩ := not_subset.mp hsub
    have hyx : y ⊆ x := by
      intro j hj
      by_cases hji : j.val ≤ i.val
      · exact hpx i hi j hji (hey j hj)
      · exact (hiy (hpy j hj i (by omega) (hex i hi))).elim
    have heq := eq_of_subset_of_card_le hyx hcard.le
    exact heq.symm

end PottsDiscontinuity.SixVertex
