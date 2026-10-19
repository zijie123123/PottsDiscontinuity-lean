module

public import PottsDiscontinuity.Bethe.AsymptoticPartition

/-! # Spatial control of the offset step function -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- Adjacent weighted bounds telescope into a Lipschitz bound at every pair
of roots. -/
theorem abs_sub_le_mul_root_dist {k : ℕ} (q u : Fin (k + 1) → ℝ) {K : ℝ}
    (hq : Monotone q)
    (hstep : ∀ j : Fin k,
      |u j.succ - u j.castSucc| ≤ K * (q j.succ - q j.castSucc))
    (i j : Fin (k + 1)) : |u i - u j| ≤ K * |q i - q j| := by
  have hplus : Monotone (fun j => K * q j + u j) :=
    Fin.monotone_iff_le_succ.mpr (fun j => by have := (abs_le.mp (hstep j)).1; linarith)
  have hminus : Monotone (fun j => K * q j - u j) :=
    Fin.monotone_iff_le_succ.mpr (fun j => by have := (abs_le.mp (hstep j)).2; linarith)
  have hdir (a b : Fin (k + 1)) (hab : a ≤ b) :
      |u b - u a| ≤ K * (q b - q a) := by
    apply abs_le.mpr
    constructor <;> linarith [hplus hab, hminus hab]
  rcases le_total i j with hij | hji
  · have hi := hdir i j hij
    rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.mpr (hq hij))]
    simpa only [neg_sub] using hi
  · have hi := hdir j i hji
    simpa only [abs_of_nonneg (sub_nonneg.mpr (hq hji))] using hi

theorem exists_interior_root_cell {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    {x : ℝ} (hleft : q ⟨0, hn⟩ ≤ x) (hright : x < q ⟨n - 1, by omega⟩) :
    ∃ j : Fin n, ∃ hj : j.val + 1 < n,
      q j ≤ x ∧ x < q ⟨j.val + 1, hj⟩ := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun j => q j ≤ x)
  have hs : s.Nonempty := ⟨⟨0, hn⟩, by simpa [s] using hleft⟩
  let j := s.max' hs
  have hjmem : j ∈ s := s.max'_mem hs
  have hjx : q j ≤ x := (Finset.mem_filter.mp hjmem).2
  have hjnext : j.val + 1 < n := by
    by_contra h
    have he : j = ⟨n - 1, by omega⟩ := Fin.ext (by
      change j.val = n - 1
      have := j.isLt
      omega)
    rw [he] at hjx
    linarith
  refine ⟨j, hjnext, hjx, ?_⟩
  by_contra h
  have hm : (⟨j.val + 1, hjnext⟩ : Fin n) ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_of_not_gt h
  have hb := s.le_max' ⟨j.val + 1, hjnext⟩ hm
  change j.val + 1 ≤ j.val at hb
  omega

theorem offsetFunction_on_cell {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hn : 0 < N / 2 - r) (hq : StrictMono q)
    (j : Fin (N / 2 - r)) (hj : j.val + 1 < N / 2 - r)
    {x : ℝ} (hx : q j ≤ x ∧ x < q ⟨j.val + 1, hj⟩) :
    offsetFunction N r h4 hr p q hn x = offsetDisplacement N r h4 hr p q j := by
  have hl : ¬x < q ⟨0, hn⟩ := by
    have := hq.monotone (show (⟨0, hn⟩ : Fin (N / 2 - r)) ≤ j from by change 0 ≤ j.val; omega)
    linarith [hx.1]
  have hu : ¬q ⟨N / 2 - r - 1, by omega⟩ ≤ x := by
    have := hq.monotone (show (⟨j.val + 1, hj⟩ : Fin (N / 2 - r)) ≤
      ⟨N / 2 - r - 1, by omega⟩ from by change j.val + 1 ≤ N / 2 - r - 1; omega)
    linarith [hx.2]
  classical
  unfold offsetFunction
  dsimp only
  rw [ite_eq_right hl, ite_eq_right hu, Finset.sum_eq_single j]
  · simp only [dite_eq_left hj, ite_eq_left hx]
  · intro k _ hkj
    by_cases hk : k.val + 1 < N / 2 - r
    · rw [dite_eq_left hk]
      apply ite_eq_right
      intro hkx
      rcases lt_or_gt_of_ne hkj with hlt | hgt
      · have hm := hq.monotone (show (⟨k.val + 1, hk⟩ : Fin (N / 2 - r)) ≤ j from
          by change k.val + 1 ≤ j.val; exact hlt)
        linarith [hx.1, hkx.2]
      · have hm := hq.monotone (show (⟨j.val + 1, hj⟩ : Fin (N / 2 - r)) ≤ k from
          by change j.val + 1 ≤ k.val; exact hgt)
        linarith [hx.2, hkx.1]
    · simp only [dite_eq_right hk]
  · simp

/-- Every step value comes from a root within one mesh size, including the
two boundary half-cells. -/
theorem offsetFunction_near_root {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hn : 0 < N / 2 - r) (hq : q ∈ S_n (N / 2 - r)) {d x : ℝ}
    (hmesh : ∀ j : Fin (N / 2 - r + 1),
      rootPartitionPoint (N / 2 - r) q hn j.succ -
        rootPartitionPoint (N / 2 - r) q hn j.castSucc ≤ d)
    (hx : x ∈ Icc (-Real.pi) Real.pi) :
    ∃ j, offsetFunction N r h4 hr p q hn x = offsetDisplacement N r h4 hr p q j ∧
      |x - q j| ≤ d := by
  have hfirst : q ⟨0, hn⟩ + Real.pi ≤ d := by
    have hm := hmesh ⟨0, by omega⟩
    change rootPartitionPoint (N / 2 - r) q hn ⟨1, by omega⟩ -
      rootPartitionPoint (N / 2 - r) q hn ⟨0, by omega⟩ ≤ d at hm
    rw [rootPartitionPoint_zero, rootPartitionPoint_root q hn ⟨0, hn⟩] at hm
    have hb := (hq.1 ⟨N / 2 - r - 1, by omega⟩).2
    linarith
  have hlast : Real.pi - q ⟨N / 2 - r - 1, by omega⟩ ≤ d := by
    have hm := hmesh ⟨N / 2 - r, by omega⟩
    have he₁ : (⟨N / 2 - r, by omega⟩ : Fin (N / 2 - r + 1)).succ =
        ⟨N / 2 - r + 1, by omega⟩ := rfl
    have he₂ : (⟨N / 2 - r, by omega⟩ : Fin (N / 2 - r + 1)).castSucc =
        ⟨(N / 2 - r - 1) + 1, by omega⟩ := Fin.ext (by
          change N / 2 - r = (N / 2 - r - 1) + 1
          omega)
    rw [he₁, he₂, rootPartitionPoint_end,
      rootPartitionPoint_root q hn ⟨N / 2 - r - 1, by omega⟩] at hm
    have hb := (hq.1 ⟨0, hn⟩).1
    linarith
  by_cases hl : x < q ⟨0, hn⟩
  · refine ⟨⟨0, hn⟩, ?_, ?_⟩
    · simp only [offsetFunction, hl, ite_eq_left]
    · rw [abs_of_nonpos (by linarith)]
      linarith [hx.1]
  by_cases hu : q ⟨N / 2 - r - 1, by omega⟩ ≤ x
  · refine ⟨⟨N / 2 - r - 1, by omega⟩, ?_, ?_⟩
    · simp [offsetFunction, hl, hu]
    · rw [abs_of_nonneg (by linarith)]
      linarith [hx.2]
  obtain ⟨j, hj, hjx⟩ := exists_interior_root_cell hn q (le_of_not_gt hl) (lt_of_not_ge hu)
  refine ⟨j, offsetFunction_on_cell h4 hr hn hq.2.1 j hj hjx, ?_⟩
  have hm := hmesh ⟨j.val + 1, by omega⟩
  have he₁ : (⟨j.val + 1, by omega⟩ : Fin (N / 2 - r + 1)).castSucc =
      ⟨j.val + 1, by omega⟩ := rfl
  have he₂ : (⟨j.val + 1, by omega⟩ : Fin (N / 2 - r + 1)).succ =
      ⟨(j.val + 1) + 1, by omega⟩ := rfl
  rw [he₁, he₂, rootPartitionPoint_root q hn j,
    rootPartitionPoint_root q hn ⟨j.val + 1, hj⟩] at hm
  rw [abs_of_nonneg (sub_nonneg.mpr hjx.1)]
  linarith [hjx.2]

end PottsDiscontinuity.Bethe
