module

public import PottsDiscontinuity.SixVertex.TransferMatrix
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Irreducibility and primitivity of the blocks `V^{[n]}`

For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` of the transfer matrix is irreducible and primitive
(some power has all entries positive); this is the statement "each block `V^{[n]}` satisfies the
assumption of the Perron–Frobenius theorem" of the paper (companion paper `blocks-are-Perron-Frobenius`).

Proof: a "single particle jump" `x ↦ (x \ {i}) ∪ {j}` (`j < i`, `i ∈ x`, `j ∉ x`) produces an interlaced
pair (the counting functions differ by the indicator of `[j, i)`), hence a positive entry of `V`;
by such jumps every `x` reaches the packed state `{0, …, n-1}`; the diagonal of `V` is `2 > 0`, so
irreducibility implies primitivity.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ} {c : ℝ}

/-! ### Generic facts on nonnegative matrices -/

section Generic

variable {S : Type*} [Fintype S] [DecidableEq S] {A : Matrix S S ℝ}

theorem pow_succ_apply_pos (hA : ∀ i j, 0 ≤ A i j) {k : ℕ} {a b c : S}
    (h1 : 0 < (A ^ k) a b) (h2 : 0 < A b c) : 0 < (A ^ (k + 1)) a c := by
  rw [pow_succ, Matrix.mul_apply]
  refine Finset.sum_pos' (fun d _ => mul_nonneg (Matrix.pow_apply_nonneg hA k a d) (hA d c))
    ⟨b, mem_univ b, mul_pos h1 h2⟩

theorem exists_pow_pos_of_reflTransGen (hA : ∀ i j, 0 ≤ A i j) {a b : S}
    (h : Relation.ReflTransGen (fun i j => 0 < A i j) a b) : ∃ k, 0 < (A ^ k) a b := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, pow_succ_apply_pos hA hk hbc⟩

theorem reflTransGen_symm_of_symm {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    {a b : α} (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hR _ _ hbc) ih

/-- A nonnegative matrix with positive diagonal in which every entry is positive in some power
is primitive. -/
theorem isPrimitive_of_pos_diag (hA : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < A i i)
    (hpow : ∀ i j, ∃ k, 0 < (A ^ k) i j) : A.IsPrimitive := by
  choose k hk using hpow
  have hpad : ∀ i j (K : ℕ), k i j ≤ K → 0 < (A ^ K) i j := by
    intro i j K hK
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
    induction d with
    | zero => exact hk i j
    | succ d ih =>
      rw [← add_assoc]
      exact pow_succ_apply_pos hA (ih (Nat.le_add_right _ _)) (hd j)
  refine ⟨hA, (Finset.univ.sup fun p : S × S => k p.1 p.2) + 1, Nat.succ_pos _, fun i j => ?_⟩
  refine hpad i j _ ?_
  have : k i j ≤ Finset.univ.sup fun p : S × S => k p.1 p.2 :=
    Finset.le_sup (f := fun p : S × S => k p.1 p.2) (mem_univ (i, j))
  omega

end Generic

/-! ### Counting along a particle jump -/

/-- The state obtained from `p` by moving the entry `i` to the vacant position `j`. -/
def jump (p : Finset (Fin N)) (i j : Fin N) : Finset (Fin N) := insert j (p.erase i)

theorem cnt_jump {p : Finset (Fin N)} {i j : Fin N} (hi : i ∈ p) (hj : j ∉ p) (hji : j < i)
    (t : Fin N) :
    cnt (jump p i j) t = cnt p t + if j ≤ t ∧ t < i then 1 else 0 := by
  unfold cnt jump
  have hjF : j ∉ p.filter (· ≤ t) := fun h => hj (mem_filter.1 h).1
  rw [Finset.filter_insert, Finset.filter_erase]
  by_cases hjt : j ≤ t
  · by_cases hit : i ≤ t
    · have hiF : i ∈ p.filter (· ≤ t) := mem_filter.2 ⟨hi, hit⟩
      have : ¬ (t < i) := not_lt.2 hit
      simp only [hjt, ↓reduceIte, this, and_false]
      rw [card_insert_of_notMem (fun h => hjF (mem_of_mem_erase h)), card_erase_of_mem hiF]
      have := card_pos.2 ⟨i, hiF⟩
      omega
    · have hiF : i ∉ p.filter (· ≤ t) := fun h => hit (mem_filter.1 h).2
      have : t < i := not_le.1 hit
      simp only [hjt, ↓reduceIte, this, and_self]
      rw [erase_eq_of_notMem hiF, card_insert_of_notMem hjF]
  · have hit : ¬ i ≤ t := fun h => hjt (le_trans hji.le h)
    have hiF : i ∉ p.filter (· ≤ t) := fun h => hit (mem_filter.1 h).2
    simp only [hjt, ↓reduceIte, false_and, add_zero]
    rw [erase_eq_of_notMem hiF]

theorem card_jump {p : Finset (Fin N)} {i j : Fin N} (hi : i ∈ p) (hj : j ∉ p) :
    (jump p i j).card = p.card := by
  unfold jump
  have : j ∉ p.erase i := fun h => hj (mem_of_mem_erase h)
  rw [card_insert_of_notMem this, card_erase_of_mem hi]
  have := card_pos.2 ⟨i, hi⟩
  omega

theorem interlaced_jump {p : Finset (Fin N)} {i j : Fin N} (hi : i ∈ p) (hj : j ∉ p)
    (hji : j < i) : Interlaced p (jump p i j) := by
  rw [interlaced_iff]
  refine ⟨(card_jump hi hj).symm, Or.inr fun t => ?_⟩
  rw [cnt_jump hi hj hji]
  constructor <;> split_ifs <;> omega

/-! ### Reaching the packed state -/

/-- The packed state `{0, …, n - 1}`. -/
def packedSet (N n : ℕ) : Finset (Fin N) := univ.filter fun a => a.val < n

theorem card_packedSet {n : ℕ} (hn : n ≤ N) : (packedSet N n).card = n := by
  unfold packedSet
  rw [← card_image_of_injective _ Fin.val_injective]
  have : (univ.filter fun a : Fin N => a.val < n).image Fin.val = range n := by
    ext k
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hk; exact ⟨⟨k, lt_of_lt_of_le hk hn⟩, hk, rfl⟩
  rw [this, card_range]

/-- The packed state as an element of `State N n`. -/
def packed (hn : n ≤ N) : State N n := ⟨packedSet N n, card_packedSet hn⟩

/-- The relation "`V^{[n]}` has a positive entry" generates a connected graph. -/
theorem reach_packed (hc : 0 < c) (hn : n ≤ N) :
    ∀ m : ℕ, ∀ x : State N n, (x.1.filter fun a => n ≤ a.val).card = m →
      Relation.ReflTransGen (fun a b : State N n => 0 < transferBlock N c n a b) x (packed hn) := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have hsub : x.1 ⊆ packedSet N n := by
      intro a ha
      by_contra hna
      have : a ∈ x.1.filter fun a => n ≤ a.val := by
        rw [mem_filter]
        refine ⟨ha, ?_⟩
        have : ¬ a.val < n := fun h => hna (by simp [packedSet, h])
        omega
      rw [card_eq_zero] at hx
      simp [hx] at this
    have : x.1 = packedSet N n :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_packedSet hn, x.2])
    have hxp : x = packed hn := Subtype.ext this
    rw [hxp]
  | succ m ih =>
    intro x hx
    have hne : (x.1.filter fun a => n ≤ a.val).Nonempty := by
      rw [← card_pos, hx]; exact Nat.succ_pos _
    obtain ⟨i, hi⟩ := hne
    rw [mem_filter] at hi
    -- a vacant position below `n`
    have hj : ∃ j : Fin N, j.val < n ∧ j ∉ x.1 := by
      by_contra hcon
      push Not at hcon
      have hsub : packedSet N n ⊆ x.1 := fun a ha => hcon a (by simpa [packedSet] using ha)
      have : packedSet N n = x.1 :=
        Finset.eq_of_subset_of_card_le hsub (by rw [card_packedSet hn, x.2])
      have hi' : i ∈ packedSet N n := this ▸ hi.1
      simp [packedSet] at hi'
      omega
    obtain ⟨j, hjn, hjx⟩ := hj
    have hji : j < i := by
      rw [Fin.lt_def]; omega
    let q : State N n := ⟨jump x.1 i j, by rw [card_jump hi.1 hjx, x.2]⟩
    have hq : (q.1.filter fun a => n ≤ a.val).card = m := by
      have : q.1.filter (fun a => n ≤ a.val) = (x.1.filter fun a => n ≤ a.val).erase i := by
        show (jump x.1 i j).filter _ = _
        unfold jump
        rw [Finset.filter_insert, Finset.filter_erase]
        have : ¬ n ≤ j.val := by omega
        simp [this]
      rw [this, card_erase_of_mem (mem_filter.2 hi), hx]
      rfl
    have hstep : 0 < transferBlock N c n x q := by
      rw [transferBlock_pos_iff hc]
      exact Or.inr (interlaced_jump hi.1 hjx hji)
    exact Relation.ReflTransGen.head hstep (ih q hq)

theorem exists_pow_pos_block (hc : 0 < c) (hn : n ≤ N) (x y : State N n) :
    ∃ k, 0 < (transferBlock N c n ^ k) x y := by
  have hA := transferBlock_nonneg (N := N) hc.le n
  have hxp := reach_packed hc hn _ x rfl
  have hyp := reach_packed hc hn _ y rfl
  have hsymm : ∀ a b : State N n, 0 < transferBlock N c n a b → 0 < transferBlock N c n b a := by
    intro a b h
    rw [transferBlock_apply, transferMatrix_symm] at h
    exact h
  exact exists_pow_pos_of_reflTransGen hA
    (hxp.trans (reflTransGen_symm_of_symm hsymm hyp))

/-- For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` is primitive. -/
theorem transferBlock_isPrimitive (hc : 0 < c) (hn : n ≤ N) :
    (transferBlock N c n).IsPrimitive :=
  isPrimitive_of_pos_diag (transferBlock_nonneg (N := N) hc.le n)
    (fun x => by rw [transferBlock_apply_self]; norm_num) (exists_pow_pos_block hc hn)

/-- For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` is irreducible. -/
theorem transferBlock_isIrreducible (hc : 0 < c) (hn : n ≤ N) :
    (transferBlock N c n).IsIrreducible :=
  (transferBlock_isPrimitive hc hn).isIrreducible

end PottsDiscontinuity.SixVertex
