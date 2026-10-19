module

public import PottsDiscontinuity.BetheAnsatz.GapReindex

/-!
# The gap weight equals the actual transfer weight

Each gap coordinate agrees with a row particle modulo N exactly at a gap endpoint.
This proves the extended-weight formula, including the endpoint across the seam.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

/-- Within a gap, the only residues occupied by the base row are its endpoints. -/
theorem gap_coordinate_occupied_iff {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hspan : x (Fin.last n) - x 0 < (N : ℤ))
    (hy : y ∈ gapTuples N x) (k : Fin (n + 1)) :
    (∃ j, y k % (N : ℤ) = x j % (N : ℤ)) ↔
      y k = cyclicPredecessorPositions N x k ∨ y k = x k := by
  have hbase : ∀ j, x (Fin.last n) - N < x j ∧ x j ≤ x (Fin.last n) := by
    intro j
    have h0 := hx.monotone (Fin.zero_le j)
    exact ⟨by omega, hx.monotone (Fin.le_last j)⟩
  have hb := gapTuples_global_bounds hx hy k
  have hu := ((mem_gapTuples.mp hy) k).2
  constructor
  · rintro ⟨j, he⟩
    have hd : (N : ℤ) ∣ x j - y k := Int.modEq_iff_dvd.mp he
    have hxj := hbase j
    have heq : x j = y k ∨ x j - y k = N := by
      by_cases hp : x j - y k = N
      · exact Or.inr hp
      · left
        have hz := Int.eq_zero_of_abs_lt_dvd hd (show |x j - y k| < (N : ℤ) from
          abs_lt.mpr ⟨by omega, by omega⟩)
        omega
    rcases heq with heq | hp
    · induction k using Fin.cases with
      | zero =>
        have hx0 := hx.monotone (Fin.zero_le j)
        exact Or.inr (by omega)
      | succ k =>
        have hl := ((mem_gapTuples.mp hy) k.succ).1
        rw [cyclicPredecessorPositions_succ] at hl
        by_cases hj : j ≤ k.castSucc
        · have hjx := hx.monotone hj
          exact Or.inl (by rw [cyclicPredecessorPositions_succ]; omega)
        · have hj' : k.succ ≤ j := by
            change k.val + 1 ≤ j.val
            have hnj : ¬ j.val ≤ k.val := hj
            omega
          have hjx := hx.monotone hj'
          exact Or.inr (by omega)
    · have hyk : y k = x (Fin.last n) - N := by omega
      have hk : k = 0 := by
        by_contra hk
        obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.mpr hk
        have hl := ((mem_gapTuples.mp hy) l.succ).1
        rw [cyclicPredecessorPositions_succ] at hl
        have hxl := hbase l.castSucc
        omega
      left
      rw [hk, cyclicPredecessorPositions_zero]
      simpa only [hk] using hyk
  · rintro (hl | hu)
    · induction k using Fin.cases with
      | zero =>
        refine ⟨Fin.last n, ?_⟩
        rw [hl, cyclicPredecessorPositions_zero]
        simp
      | succ k =>
        refine ⟨k.castSucc, ?_⟩
        rw [hl, cyclicPredecessorPositions_succ]
    · exact ⟨k, by rw [hu]⟩

/-- Rewrite the extended weight as a product testing occupied residues. -/
theorem gapWeight_eq_residue_product {N n : ℕ} (c : ℝ) {x y : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hspan : x (Fin.last n) - x 0 < (N : ℤ))
    (hy : y ∈ gapTuples N x) :
    gapWeight c N x y =
      ∏ k, if (∃ j, y k % (N : ℤ) = x j % (N : ℤ)) then 1 else (c : ℂ) ^ 2 := by
  unfold gapWeight
  apply Finset.prod_congr rfl
  intro k _
  simp only [gap_coordinate_occupied_iff hx hspan hy]

/-- The exponent in (1.5) is twice the number of particles of y outside x. -/
theorem transfer_exponent_eq_twice_sdiff {N : ℕ} {x y : Finset (Fin N)} (hcard : x.card = y.card) :
    (univ.filter fun i => Psi x i ≠ Psi y i).card = 2 * (y \ x).card := by
  have he : (univ.filter fun i => Psi x i ≠ Psi y i) = (x \ y) ∪ (y \ x) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_sdiff]
    by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp [Psi, hx, hy]
  have hd : Disjoint (x \ y) (y \ x) := disjoint_left.mpr fun i hi hj =>
    (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  rw [he, card_union_of_disjoint hd, Finset.card_sdiff_comm hcard]
  omega

/-- Enumerating occupied residues of an actual state recovers its membership test. -/
theorem positions_occupied_iff {N n : ℕ} (x : State N n) (i : Fin N) :
    (∃ j, (i.val : ℤ) % (N : ℤ) = positions x j % (N : ℤ)) ↔ i ∈ x.1 := by
  have hi : (i.val : ℤ) % (N : ℤ) = i.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
  simp only [hi]
  constructor
  · rintro ⟨j, hj⟩
    have hpos := (mem_orderedTuples.mp (positions_mem_orderedTuples x)).1 j
    rw [Int.emod_eq_of_lt hpos.1 hpos.2] at hj
    have he : x.1.orderEmbOfFin x.2 j = i := by
      apply Fin.ext
      unfold positions at hj
      exact_mod_cast hj.symm
    rw [← he]
    exact orderEmbOfFin_mem _ _ _
  · intro hi
    have hr : i ∈ Set.range (x.1.orderEmbOfFin x.2) := by
      rw [range_orderEmbOfFin]
      exact hi
    obtain ⟨j, rfl⟩ := hr
    refine ⟨j, ?_⟩
    change positions x j = positions x j % (N : ℤ)
    have hpos := (mem_orderedTuples.mp (positions_mem_orderedTuples x)).1 j
    exact (Int.emod_eq_of_lt hpos.1 hpos.2).symm

/-- Product of the outside-particle weights, in the actual increasing enumeration. -/
theorem positions_outside_product {N m : ℕ} (c : ℝ) (x y : State N m) :
    (∏ k, if y.1.orderEmbOfFin y.2 k ∈ x.1 then (1 : ℂ) else (c : ℂ) ^ 2) =
      (c : ℂ) ^ (univ.filter fun i => Psi x.1 i ≠ Psi y.1 i).card := by
  calc
    _ = ∏ i ∈ y.1, if i ∈ x.1 then (1 : ℂ) else (c : ℂ) ^ 2 := by
      calc
        _ = ∏ i ∈ univ.image (y.1.orderEmbOfFin y.2),
            if i ∈ x.1 then (1 : ℂ) else (c : ℂ) ^ 2 :=
          (Finset.prod_image (y.1.orderEmbOfFin y.2).injective.injOn).symm
        _ = _ := by rw [image_orderEmbOfFin_univ]
    _ = ((c : ℂ) ^ 2) ^ (y.1 \ x.1).card := by
      rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
        Finset.filter_notMem_eq_sdiff]
    _ = _ := by
      rw [← pow_mul, transfer_exponent_eq_twice_sdiff (x.2.trans y.2.symm)]

/-- The lower orientation's gap weight is the exact complexified entry weight. -/
theorem gapWeight_positions {N n : ℕ} (c : ℝ) (x y : State N (n + 1))
    (hy : positions y ∈ gapTuples N (positions x)) :
    gapWeight c N (positions x) (positions y) =
      (c : ℂ) ^ (univ.filter fun i => Psi x.1 i ≠ Psi y.1 i).card := by
  rw [gapWeight_eq_residue_product c (positions_strictMono x) (positions_span_lt x) hy]
  have he : ∀ k, (∃ j, positions y k % (N : ℤ) = positions x j % (N : ℤ)) ↔
      y.1.orderEmbOfFin y.2 k ∈ x.1 := fun k => positions_occupied_iff x _
  simp_rw [he]
  exact positions_outside_product c x y

/-- The shifted upper orientation has the same actual entry weight, including the seam. -/
theorem gapWeight_shift_positions {N n : ℕ} (c : ℝ) (x y : State N (n + 1))
    (hy : cyclicPredecessorPositions N (positions y) ∈ gapTuples N (positions x)) :
    gapWeight c N (positions x) (cyclicPredecessorPositions N (positions y)) =
      (c : ℂ) ^ (univ.filter fun i => Psi x.1 i ≠ Psi y.1 i).card := by
  rw [gapWeight_eq_residue_product c (positions_strictMono x) (positions_span_lt x) hy]
  simp_rw [cyclicPredecessor_residue]
  rw [Equiv.prod_comp (finRotate (n + 1)).symm (fun k =>
    if (∃ j, positions y k % (N : ℤ) = positions x j % (N : ℤ)) then (1 : ℂ) else (c : ℂ) ^ 2)]
  have he : ∀ k, (∃ j, positions y k % (N : ℤ) = positions x j % (N : ℤ)) ↔
      y.1.orderEmbOfFin y.2 k ∈ x.1 := fun k => positions_occupied_iff x _
  simp_rw [he]
  exact positions_outside_product c x y

end PottsDiscontinuity.BetheAnsatz
