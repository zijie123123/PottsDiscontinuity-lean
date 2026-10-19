module

public import PottsDiscontinuity.Torus.NetEuler
public import PottsDiscontinuity.TorusLoops.WindingLoopCount
public import PottsDiscontinuity.TorusRC.Measure

/-!
# The normalized loop observable on the finite torus

The observable is `(2 / sqrt q)^ell₀ q^{-s}` with the fixed homological
definition of `ell₀`. This file records the finite-volume pointwise bounds used
to estimate its expectation from a tail bound.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC

variable {N M : ℕ}

noncomputable section

/-- The base of the source loop factor. -/
noncomputable def windingLoopDensityBase (q : Set.Ici (1 : ℝ)) : ℝ :=
  2 / Real.sqrt q.val

/-- An upper base at least one and at least the source loop-factor base. -/
noncomputable def windingLoopDensityUpperBase (q : Set.Ici (1 : ℝ)) : ℝ :=
  max 1 (windingLoopDensityBase q)

/-- A lower base at most one and at most the source loop-factor base. -/
noncomputable def windingLoopDensityLowerBase (q : Set.Ici (1 : ℝ)) : ℝ :=
  min 1 (windingLoopDensityBase q)

/-- The source observable, using the OR-2 winding count and the net indicator. -/
noncomputable def windingLoopDensityWeight
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) : ℝ :=
  windingLoopDensityBase q ^ windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A /
    q.val ^ rcNetIndicator hN hM A

/-- The finite torus expectation of `(2 / sqrt q)^ell₀ q^{-s}`. -/
noncomputable def phi_T_windingLoopDensityExpectation
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) : ℝ :=
  ∑ A, torusRCMass hN hM q A * windingLoopDensityWeight hN hM hNp hMp q A

theorem windingLoopDensityBase_pos (q : Set.Ici (1 : ℝ)) :
    0 < windingLoopDensityBase q := by
  unfold windingLoopDensityBase
  exact div_pos (by norm_num) (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one q.property))

theorem windingLoopDensityUpperBase_ge_one (q : Set.Ici (1 : ℝ)) :
    1 ≤ windingLoopDensityUpperBase q := by
  exact le_max_left _ _

theorem windingLoopDensityUpperBase_ge_base (q : Set.Ici (1 : ℝ)) :
    windingLoopDensityBase q ≤ windingLoopDensityUpperBase q := by
  exact le_max_right _ _

theorem windingLoopDensityLowerBase_pos (q : Set.Ici (1 : ℝ)) :
    0 < windingLoopDensityLowerBase q := by
  exact lt_min zero_lt_one (windingLoopDensityBase_pos q)

theorem windingLoopDensityLowerBase_le_one (q : Set.Ici (1 : ℝ)) :
    windingLoopDensityLowerBase q ≤ 1 := by
  exact min_le_left _ _

theorem rcNetIndicator_eq_zero_or_one (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : rcNetIndicator hN hM A = 0 ∨ rcNetIndicator hN hM A = 1 := by
  classical
  unfold rcNetIndicator
  split_ifs <;> simp

theorem windingLoopDensityWeight_pos (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    0 < windingLoopDensityWeight hN hM hNp hMp q A := by
  unfold windingLoopDensityWeight
  exact div_pos (pow_pos (windingLoopDensityBase_pos q) _)
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)

theorem windingLoopDensityWeight_le_of_count_le
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) (A : RCConfig N M)
    (hcount : windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A ≤ m) :
    windingLoopDensityWeight hN hM hNp hMp q A ≤
      windingLoopDensityUpperBase q ^ m := by
  let ℓ := windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A
  have hℓ : ℓ ≤ m := hcount
  have hqval : (1 : ℝ) ≤ q.val := q.property
  have hqpow : 1 ≤ q.val ^ rcNetIndicator hN hM A := by
    rcases rcNetIndicator_eq_zero_or_one hN hM A with hs | hs
    · rw [hs]
      simp
    · rw [hs]
      simpa using hqval
  have hnum : windingLoopDensityBase q ^ ℓ ≤
      windingLoopDensityUpperBase q ^ m := by
    calc
      windingLoopDensityBase q ^ ℓ ≤ windingLoopDensityUpperBase q ^ ℓ :=
        pow_le_pow_left₀ (windingLoopDensityBase_pos q).le
          (windingLoopDensityUpperBase_ge_base q) _
      _ ≤ windingLoopDensityUpperBase q ^ m := by
        exact pow_le_pow_right₀ (windingLoopDensityUpperBase_ge_one q) hℓ
  unfold windingLoopDensityWeight
  dsimp [ℓ] at hnum hqpow
  exact (div_le_self (pow_nonneg (windingLoopDensityBase_pos q).le _) hqpow).trans hnum

theorem windingLoopDensityWeight_le_global
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    windingLoopDensityWeight hN hM hNp hMp q A ≤
      windingLoopDensityUpperBase q ^ (N + M) := by
  apply windingLoopDensityWeight_le_of_count_le hN hM hNp hMp q (N + M) A
  exact windingLoopCount_le hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A

theorem windingLoopDensityWeight_ge_of_count_lt
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) (A : RCConfig N M)
    (hcount : windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A < m) :
    windingLoopDensityLowerBase q ^ m / q.val ≤
      windingLoopDensityWeight hN hM hNp hMp q A := by
  let ℓ := windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A
  have hℓ : ℓ ≤ m := Nat.le_of_lt hcount
  have hsLow : windingLoopDensityLowerBase q ^ m ≤
      windingLoopDensityBase q ^ ℓ := by
    by_cases ht : windingLoopDensityBase q ≤ 1
    · calc
        windingLoopDensityLowerBase q ^ m = windingLoopDensityBase q ^ m := by
          change (min 1 (windingLoopDensityBase q)) ^ m = _
          rw [min_eq_right ht]
        _ ≤ windingLoopDensityBase q ^ ℓ :=
          pow_le_pow_of_le_one (windingLoopDensityBase_pos q).le ht hℓ
    · have hbase : 1 ≤ windingLoopDensityBase q := le_of_not_ge ht
      calc
        windingLoopDensityLowerBase q ^ m ≤ 1 ^ m :=
          pow_le_pow_left₀ (windingLoopDensityLowerBase_pos q).le
            (windingLoopDensityLowerBase_le_one q) _
        _ = 1 := by simp
        _ ≤ windingLoopDensityBase q ^ ℓ := one_le_pow₀ hbase
  have hqval : (1 : ℝ) ≤ q.val := q.property
  have hqpow : q.val ^ rcNetIndicator hN hM A ≤ q.val := by
    rcases rcNetIndicator_eq_zero_or_one hN hM A with hs | hs
    · rw [hs]
      simpa using hqval
    · rw [hs]
      simp
  have hden : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  have hdenR : 0 < q.val ^ rcNetIndicator hN hM A := pow_pos hden _
  have hratio : windingLoopDensityLowerBase q ^ m / q.val ≤
      windingLoopDensityBase q ^ ℓ /
        q.val ^ rcNetIndicator hN hM A := by
    calc
      windingLoopDensityLowerBase q ^ m / q.val ≤
          windingLoopDensityBase q ^ ℓ / q.val :=
        div_le_div_of_nonneg_right hsLow hden.le
      _ ≤ windingLoopDensityBase q ^ ℓ /
          q.val ^ rcNetIndicator hN hM A :=
        div_le_div_of_nonneg_left
          (pow_nonneg (windingLoopDensityBase_pos q).le _) hdenR hqpow
  unfold windingLoopDensityWeight
  dsimp [ℓ] at hratio
  exact hratio

end

end PottsDiscontinuity.TorusLoops
