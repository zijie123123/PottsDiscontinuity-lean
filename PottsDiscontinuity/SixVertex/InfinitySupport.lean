module

public import PottsDiscontinuity.SixVertex.InfinityLimit
public import PottsDiscontinuity.SixVertex.RowTransfer

/-!
# Support of the infinite-anisotropy block

The no-consecutive-up-arrow reduction in Lemma 3.2, including the cyclic seam.
We use the already proved row flux equation rather than an informal interlacing picture.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

/-- Up arrows form an independent set of the cyclic row. -/
def NoConsecutiveUp (x : Finset (Fin N)) : Prop := ∀ i ∈ x, nxt i ∉ x

/-- Down arrows preceded by another down arrow, including the seam of the cycle. -/
def defects (x : Finset (Fin N)) : Finset (Fin N) :=
  univ.filter fun i => i ∉ x ∧ prv i ∉ x

/-- An interlaced pair admits horizontal arrows satisfying the row ice rule. -/
theorem exists_flux_of_interlaced {x y : Finset (Fin N)} (hi : Interlaced x y) :
    ∃ h : Fin N → Bool, Flux x y h := by
  cases N with
  | zero => exact ⟨fun _ => false, fun i => Fin.elim0 i⟩
  | succ k =>
    rcases (interlaced_iff_validS x y).1 hi with hs | hs
    · exact ⟨hOf x y false, flux_hOf hs⟩
    · exact ⟨hOf x y true, flux_hOf hs⟩

private theorem toInt_bounds (b : Bool) : 0 ≤ toInt b ∧ toInt b ≤ 1 := by
  cases b <;> norm_num [toInt]

/-- Disjoint interlaced states cannot have adjacent up arrows, even across `N-1 | 0`. -/
theorem noConsecutiveUp_of_interlaced_disjoint {x y : Finset (Fin N)}
    (hi : Interlaced x y) (hd : Disjoint x y) : NoConsecutiveUp x := by
  obtain ⟨h, hf⟩ := exists_flux_of_interlaced hi
  intro i hix hnix
  have hyi := hd.notMem_of_mem_left_finset hix
  have hyni := hd.notMem_of_mem_left_finset hnix
  have h1 := hf i
  have h2 := hf (nxt i)
  have hp : prv (nxt i) = i := (finRotate N).symm_apply_apply i
  rw [hp] at h2
  simp only [hix, hnix, hyi, hyni, decide_true, decide_false, toInt,
    Bool.false_eq_true, ↓reduceIte] at h1 h2
  have h0 := toInt_bounds (h (prv i))
  have h3 := toInt_bounds (h (nxt i))
  omega

/-- Every nonzero matrix entry joins two states with no consecutive up arrows. -/
theorem infinityBlock_support (hn : 0 < n) (x y : State N n)
    (h : infinityBlock N n x y ≠ 0) : NoConsecutiveUp x.1 ∧ NoConsecutiveUp y.1 := by
  have h1 : infinityBlock N n x y = 1 := by
    unfold infinityBlock at h ⊢
    split_ifs at * <;> simp_all
  obtain ⟨hi, hd⟩ := (infinityBlock_eq_one_iff hn x y).1 h1
  exact ⟨noConsecutiveUp_of_interlaced_disjoint hi hd,
    noConsecutiveUp_of_interlaced_disjoint hi.symm hd.symm⟩

theorem infinityBlock_eq_zero_of_not_noConsecutiveUp (hn : 0 < n) (x y : State N n)
    (hx : ¬ NoConsecutiveUp x.1) : infinityBlock N n x y = 0 := by
  by_contra h
  exact hx (infinityBlock_support hn x y h).1

/-- The range of the limit operator is supported on the independent row states. -/
theorem infinityBlock_mulVec_supported (hn : 0 < n) (v : State N n → ℝ)
    (x : State N n) (hx : ¬ NoConsecutiveUp x.1) :
    (infinityBlock N n *ᵥ v) x = 0 := by
  simp only [Matrix.mulVec, dotProduct,
    infinityBlock_eq_zero_of_not_noConsecutiveUp hn x _ hx, zero_mul, sum_const_zero]

/-- Up arrows and their cyclic successors are disjoint. -/
theorem NoConsecutiveUp.disjoint_image {x : Finset (Fin N)} (hx : NoConsecutiveUp x) :
    Disjoint x (x.image nxt) := by
  apply disjoint_left.mpr
  intro i hi him
  obtain ⟨j, hj, rfl⟩ := mem_image.mp him
  exact hx j hj hi

/-- Defects are precisely the complement of the up arrows and their successors. -/
theorem defects_eq_compl (x : Finset (Fin N)) :
    defects x = (x ∪ x.image nxt)ᶜ := by
  ext i
  have he : i ∈ x.image nxt ↔ prv i ∈ x := by
    constructor
    · rintro him
      obtain ⟨j, hj, rfl⟩ := mem_image.mp him
      simpa only [prv, nxt, Equiv.symm_apply_apply] using hj
    · intro h
      exact mem_image.mpr ⟨prv i, h, (finRotate N).apply_symm_apply i⟩
  simp only [defects, mem_filter, mem_univ, true_and, mem_compl, mem_union, he, not_or]

/-- There are exactly `N - 2n` defects in a state without consecutive up arrows. -/
theorem card_defects (x : State N n) (hx : NoConsecutiveUp x.1) :
    (defects x.1).card = N - 2 * n := by
  rw [defects_eq_compl, card_compl, card_union_of_disjoint hx.disjoint_image,
    card_image_of_injective _ (finRotate N).injective, x.2, Fintype.card_fin]
  omega

/-- The source's `2r` defect count, with subtraction-free particle-number premises. -/
theorem card_defects_eq_two_mul (x : State N n) (hx : NoConsecutiveUp x.1)
    {r : ℕ} (hN : N = 2 * (n + r)) : (defects x.1).card = 2 * r := by
  rw [card_defects x hx, hN]
  omega

/-- A completely staggered configuration alternates at every cyclic edge. -/
def Staggered (x : Finset (Fin N)) : Prop := ∀ i, nxt i ∈ x ↔ i ∉ x

end PottsDiscontinuity.SixVertex
