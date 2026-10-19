module

public import PottsDiscontinuity.SixVertex.InfinitySupport
public import PottsDiscontinuity.SixVertex.Irreducible

/-!
# Moves on independent row states

Rotation is a genuine positive edge of the limiting matrix. The finite carrier
here is exactly the independent row configurations, with no extra conditions.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

instance (x : Finset (Fin N)) : Decidable (NoConsecutiveUp x) := by
  unfold NoConsecutiveUp
  infer_instance

/-- The actual nonzero-support carrier of the infinite-anisotropy block. -/
abbrev IndependentState (N n : ℕ) := {x : State N n // NoConsecutiveUp x.1}

/-- The restriction of the limit matrix to row states with no adjacent up arrows. -/
noncomputable def infinityRestriction (N n : ℕ) :
    Matrix (IndependentState N n) (IndependentState N n) ℝ :=
  (infinityBlock N n).submatrix Subtype.val Subtype.val

/-- Rotate all up arrows one site to the right. -/
def rotateUp (x : Finset (Fin N)) : Finset (Fin N) := x.image nxt

@[simp] theorem mem_rotateUp (x : Finset (Fin N)) (i : Fin N) :
    i ∈ rotateUp x ↔ prv i ∈ x := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    simpa only [prv, nxt, Equiv.symm_apply_apply] using hj
  · intro hi
    exact mem_image.mpr ⟨prv i, hi, (finRotate N).apply_symm_apply i⟩

@[simp] theorem card_rotateUp (x : Finset (Fin N)) : (rotateUp x).card = x.card :=
  card_image_of_injective _ (finRotate N).injective

theorem NoConsecutiveUp.rotateUp {x : Finset (Fin N)} (hx : NoConsecutiveUp x) :
    NoConsecutiveUp (rotateUp x) := by
  intro i hi hni
  rw [mem_rotateUp] at hi hni
  simp only [nxt, prv, Equiv.symm_apply_apply] at hni
  exact hx (prv i) hi (by simpa only [nxt, prv, Equiv.apply_symm_apply] using hni)

/-- Rotation of an independent state. -/
def rotateIndependent (x : IndependentState N n) : IndependentState N n :=
  ⟨⟨rotateUp x.1.1, (card_rotateUp _).trans x.1.2⟩, x.2.rotateUp⟩

/-- The converse to the interlacing-to-flux bridge, including the empty cycle. -/
theorem interlaced_of_flux {x y : Finset (Fin N)} {h : Fin N → Bool}
    (hf : Flux x y h) : Interlaced x y := by
  cases N with
  | zero =>
    have hy : y = x := Subsingleton.elim _ _
    rw [hy]
    exact interlaced_refl _
  | succ k =>
    have hs := validS_of_flux hf
    apply (interlaced_iff_validS _ _).mpr
    cases he : h (Fin.last k)
    · exact Or.inl (he ▸ hs)
    · exact Or.inr (he ▸ hs)

/-- A row and its one-site rotation interlace, regardless of adjacent up arrows. -/
theorem interlaced_rotateUp (x : Finset (Fin N)) : Interlaced x (rotateUp x) := by
  apply interlaced_of_flux (h := fun i => decide (i ∈ x))
  intro i
  simp only [toInt_decide_mem, mem_rotateUp]
  omega

/-- Every independent state has a positive rotation edge. -/
theorem infinityRestriction_rotate (hn : 0 < n) (x : IndependentState N n) :
    infinityRestriction N n x (rotateIndependent x) = 1 := by
  apply (infinityBlock_eq_one_iff hn x.1 (rotateIndependent x).1).mpr
  exact ⟨interlaced_rotateUp x.1.1, x.2.disjoint_image⟩

theorem infinityRestriction_nonneg (x y : IndependentState N n) :
    0 ≤ infinityRestriction N n x y := infinityBlock_nonneg _ _

theorem infinityRestriction_symm (x y : IndependentState N n) :
    infinityRestriction N n x y = infinityRestriction N n y x := infinityBlock_symm _ _

theorem infinityRestriction_isHermitian : (infinityRestriction N n).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext x y
  exact infinityRestriction_symm y x

/-- A length-two positive return is available at every independent state. -/
theorem infinityRestriction_square_self_pos (hn : 0 < n) (x : IndependentState N n) :
    0 < (infinityRestriction N n ^ 2) x x := by
  rw [pow_two, Matrix.mul_apply]
  refine sum_pos' (fun y _ => mul_nonneg (infinityRestriction_nonneg x y)
    (infinityRestriction_nonneg y x)) ⟨rotateIndependent x, mem_univ _, ?_⟩
  rw [infinityRestriction_symm (rotateIndependent x) x, infinityRestriction_rotate hn]
  norm_num

/-- Moving an up arrow one site left is admissible when the two preceding sites are vacant. -/
theorem noConsecutiveUp_jump_left {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    {i j : Fin N} (hi : i ∈ x) (hj : j ∉ x) (hp : prv j ∉ x) (hji : nxt j = i) :
    NoConsecutiveUp (jump x i j) := by
  have hij : i ≠ j := fun he => hj (he ▸ hi)
  intro k hk hnk
  simp only [jump, mem_insert, mem_erase] at hk hnk
  rcases hk with rfl | ⟨hki, hk⟩
  · rw [hji] at hnk
    rcases hnk with he | ⟨he, _⟩
    · exact hij he
    · exact he rfl
  · rcases hnk with hnj | ⟨_, hnx⟩
    · have hkprev : k = prv j := by
        rw [← hnj]
        exact ((finRotate N).symm_apply_apply k).symm
      exact hp (hkprev ▸ hk)
    · exact hx k hk hnx

/-- The row after one left slide interlaces the right rotation of the original row. -/
theorem interlaced_jump_left_rotate {x : Finset (Fin N)} {i j : Fin N}
    (hi : i ∈ x) (hj : j ∉ x) (hji : nxt j = i) :
    Interlaced (jump x i j) (rotateUp x) := by
  apply interlaced_of_flux (h := fun k => decide (k ∈ insert j x))
  intro k
  have hpi : prv i = j := by rw [← hji]; exact (finRotate N).symm_apply_apply j
  have hpk : prv k = j ↔ k = i := by
    constructor
    · intro he
      rw [← hji, ← he]
      exact ((finRotate N).apply_symm_apply k).symm
    · rintro rfl
      exact hpi
  simp only [toInt_decide_mem, mem_rotateUp, jump, mem_insert, mem_erase, hpk]
  have hij : i ≠ j := fun he => hj (he ▸ hi)
  by_cases hki : k = i
  · subst k
    simp [hpi, hi, hj, hij, toInt]
  · by_cases hkj : k = j
    · subst k
      simp [hj, hki, toInt]
    · simp [hki, hkj, toInt]

/-- A single left slide is simulated by two genuine edges of the limit matrix. -/
theorem infinityRestriction_slide_left_reachable (hn : 0 < n) (x : IndependentState N n)
    {i j : Fin N} (hi : i ∈ x.1.1) (hj : j ∉ x.1.1) (hp : prv j ∉ x.1.1)
    (hji : nxt j = i) :
    ∃ y : IndependentState N n, y.1.1 = jump x.1.1 i j ∧
      Relation.ReflTransGen (fun a b : IndependentState N n =>
        0 < infinityRestriction N n a b) x y := by
  let y : IndependentState N n :=
    ⟨⟨jump x.1.1 i j, (card_jump hi hj).trans x.1.2⟩,
      noConsecutiveUp_jump_left x.2 hi hj hp hji⟩
  refine ⟨y, rfl, Relation.ReflTransGen.head (b := rotateIndependent x) ?_ (Relation.ReflTransGen.single ?_)⟩
  · rw [infinityRestriction_rotate hn]
    norm_num
  · have hd : Disjoint (jump x.1.1 i j) (rotateUp x.1.1) := by
      apply disjoint_left.mpr
      intro k hk hr
      simp only [jump, mem_insert, mem_erase] at hk
      rcases hk with rfl | ⟨_, hk⟩
      · exact hp ((mem_rotateUp _ _).mp hr)
      · exact x.2.disjoint_image.notMem_of_mem_left_finset hk hr
    have he : infinityRestriction N n (rotateIndependent x) y = 1 :=
      (infinityBlock_eq_one_iff hn _ _).mpr
        ⟨(interlaced_jump_left_rotate hi hj hji).symm, hd.symm⟩
    rw [he]
    norm_num

end PottsDiscontinuity.SixVertex
