module

public import Mathlib

/-! # A centered discrete Gronwall estimate -/

@[expose] public section

namespace PottsDiscontinuity.Bethe

/-- Antisymmetry anchors a local recurrence at the center, including the case
where the center lies between two indices. -/
theorem centered_anchor_bound {n N : ℕ} {C : ℝ} {u : ℕ → ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) (hsmall : C ≤ N)
    (hsym : ∀ j ≤ n, u (n - j) = -u j)
    (hstep : ∀ j < n, |u (j + 1) - u j| ≤ C / N * (|u j| + 1)) :
    |u (n / 2)| ≤ C / N := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq : 0 ≤ C / N := div_nonneg hC hNp.le
  have hq1 : C / N ≤ 1 := (div_le_one hNp).mpr hsmall
  have hc : n / 2 ≤ n := Nat.div_le_self _ _
  have hs := hsym (n / 2) hc
  by_cases he : n % 2 = 0
  · have heq : n - n / 2 = n / 2 := by omega
    rw [heq] at hs
    have hz : u (n / 2) = 0 := by linarith
    simpa [hz] using hq
  · have heq : n - n / 2 = n / 2 + 1 := by omega
    rw [heq] at hs
    have hd := hstep (n / 2) (by omega)
    rw [hs, show -u (n / 2) - u (n / 2) = -(2 * u (n / 2)) by ring,
      abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hd
    have hu : |u (n / 2)| ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hq1 (by positivity : 0 ≤ |u (n / 2)| + 1)
      linarith
    have := mul_le_mul_of_nonneg_left (show |u (n / 2)| + 1 ≤ 2 by linarith) hq
    linarith

theorem discrete_gronwall_right {n c : ℕ} {q : ℝ} {u : ℕ → ℝ}
    (hq : 0 ≤ q) (hanchor : |u c| ≤ 1)
    (hstep : ∀ j < n, |u (j + 1) - u j| ≤ q * (|u j| + 1)) :
    ∀ t, c + t ≤ n → |u (c + t)| + 1 ≤ 2 * (1 + q) ^ t := by
  intro t
  induction t with
  | zero => intro _; simpa using (show |u c| + 1 ≤ 2 by linarith)
  | succ t ih =>
    intro ht
    have hi := ih (by omega)
    have hd := hstep (c + t) (by omega)
    have ha := abs_add_le (u (c + t + 1) - u (c + t)) (u (c + t))
    have hn : |u (c + t + 1)| + 1 ≤ (1 + q) * (|u (c + t)| + 1) := by
      simp only [sub_add_cancel] at ha
      nlinarith only [ha, hd]
    calc
      |u (c + (t + 1))| + 1 = |u (c + t + 1)| + 1 := by rw [Nat.add_assoc]
      _ ≤ (1 + q) * (|u (c + t)| + 1) := hn
      _ ≤ (1 + q) * (2 * (1 + q) ^ t) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = 2 * (1 + q) ^ (t + 1) := by rw [pow_succ]; ring

theorem one_add_div_pow_le_exp {N t : ℕ} {C : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) (ht : t ≤ N) :
    (1 + C / N) ^ t ≤ Real.exp C := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb : 1 + C / N ≤ Real.exp (C / N) := by
    simpa [add_comm] using Real.add_one_le_exp (C / N)
  calc
    _ ≤ (Real.exp (C / N)) ^ t := pow_le_pow_left₀ (by positivity) hb _
    _ = Real.exp ((t : ℝ) * (C / N)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp C := Real.exp_le_exp.mpr (by
      have htc : (t : ℝ) ≤ N := Nat.cast_le.mpr ht
      have := mul_le_mul_of_nonneg_right htc (div_nonneg hC hNp.le)
      simpa [mul_div_cancel₀ C hNp.ne', mul_div_assoc, mul_comm (N : ℝ) C] using this)

/-- A centered local recurrence gives a uniform bound without any prior
alignment estimate. The same bound then improves every increment to `O(1/N)`. -/
theorem centered_discrete_gronwall {n N : ℕ} {C : ℝ} {u : ℕ → ℝ}
    (hN : 0 < N) (hn : n ≤ N) (hC : 0 ≤ C) (hsmall : C ≤ N)
    (hsym : ∀ j ≤ n, u (n - j) = -u j)
    (hstep : ∀ j < n, |u (j + 1) - u j| ≤ C / N * (|u j| + 1)) :
    (∀ j ≤ n, |u j| ≤ 2 * Real.exp C) ∧
      (∀ j < n, |u (j + 1) - u j| ≤ C * (2 * Real.exp C + 1) / N) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hanchor : |u (n / 2)| ≤ 1 :=
    (centered_anchor_bound hN hC hsmall hsym hstep).trans
      ((div_le_one hNp).mpr hsmall)
  have hright : ∀ j ≤ n, n / 2 ≤ j → |u j| ≤ 2 * Real.exp C := by
    intro j hj hc
    have hi := discrete_gronwall_right (div_nonneg hC hNp.le) hanchor hstep
      (j - n / 2) (by omega)
    rw [Nat.add_sub_of_le hc] at hi
    have hp := one_add_div_pow_le_exp hN hC (show j - n / 2 ≤ N by omega)
    linarith
  have hbound : ∀ j ≤ n, |u j| ≤ 2 * Real.exp C := by
    intro j hj
    by_cases hc : n / 2 ≤ j
    · exact hright j hj hc
    · have hi := hright (n - j) (by omega) (by omega)
      simpa [hsym j hj] using hi
  refine ⟨hbound, ?_⟩
  intro j hj
  calc
    _ ≤ C / N * (|u j| + 1) := hstep j hj
    _ ≤ C / N * (2 * Real.exp C + 1) :=
      mul_le_mul_of_nonneg_left (by have := hbound j (by omega); linarith)
        (div_nonneg hC hNp.le)
    _ = C * (2 * Real.exp C + 1) / N := by ring

end PottsDiscontinuity.Bethe
