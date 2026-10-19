module

public import PottsDiscontinuity.SixVertex.InfinityChoices
public import PottsDiscontinuity.SixVertex.InfinityDescent
public import PottsDiscontinuity.SixVertex.InfinityGround
public import PottsDiscontinuity.SixVertex.InfinityPhase

/-! # Indexed choices and collision cancellation on shifted lifts -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

/-- Canonical integer version of the ordered shifted defect coordinates. -/
noncomputable def orderedDefectLift (x : Finset (Fin N)) : Fin (defects x).card → ℤ :=
  fun a => defectCoordinate x a

/-- Read indexed choices on the canonical ordered defect sites. -/
noncomputable def indexedDefectChoice (x : Finset (Fin N))
    (d : Fin (defects x).card → Bool) : DefectChoice x :=
  fun i => d ((defects x).orderIsoOfFin rfl |>.symm i)

/-- Left/right lifts with the convention `true = left` used by the defect choices. -/
def leftStepLift {k : ℕ} (x : Fin k → ℤ) (d : Fin k → Bool) : Fin k → ℤ :=
  fun a => x a + if d a then -1 else 1

private theorem sineLiftWeight_zero_of_factor {k : ℕ} (L : ℝ) (x : Fin k → ℤ)
    {a b : Fin k} (hab : a ≠ b)
    (hs : Real.sin (Real.pi * ((x b : ℝ) - x a) / L) = 0) : sineLiftWeight L x = 0 := by
  have hs' : Real.sin (Real.pi * ((x a : ℝ) - x b) / L) = 0 := by
    have ht : Real.pi * ((x a : ℝ) - x b) / L = -(Real.pi * ((x b : ℝ) - x a) / L) := by ring
    rw [ht, Real.sin_neg, hs, neg_zero]
  rcases lt_or_gt_of_ne hab with hab | hba
  · apply prod_eq_zero (mem_univ a)
    exact prod_eq_zero (mem_Ioi.mpr hab) hs
  · apply prod_eq_zero (mem_univ b)
    exact prod_eq_zero (mem_Ioi.mpr hba) hs'

theorem sineLiftWeight_zero_of_equal {k : ℕ} (L : ℝ) (x : Fin k → ℤ)
    {a b : Fin k} (hab : a ≠ b) (hx : x a = x b) : sineLiftWeight L x = 0 := by
  apply sineLiftWeight_zero_of_factor L x hab
  rw [hx]
  simp

theorem sineLiftWeight_zero_of_period_difference {k : ℕ} (P : ℤ) (hP : P ≠ 0)
    (x : Fin k → ℤ) {a b : Fin k} (hab : a ≠ b) (hx : x b - x a = P) :
    sineLiftWeight (P : ℝ) x = 0 := by
  apply sineLiftWeight_zero_of_factor (P : ℝ) x hab
  have hcast : (x b : ℝ) - x a = (P : ℝ) := by exact_mod_cast hx
  rw [hcast, mul_div_cancel_right₀ _ (Int.cast_ne_zero.mpr hP), Real.sin_pi]

/-- Canonically ordered sites a unit apart have consecutive ranks. -/
theorem orderEmbOfFin_rank_succ {k : ℕ} (s : Finset (Fin N)) (hs : s.card = k)
    (a b : Fin k) (hv : (s.orderEmbOfFin hs b).val = (s.orderEmbOfFin hs a).val + 1) :
    b.val = a.val + 1 := by
  have hab : a < b := (s.orderEmbOfFin hs).lt_iff_lt.mp (by rw [Fin.lt_def, hv]; omega)
  by_contra hne
  let c : Fin k := ⟨a.val + 1, by omega⟩
  have hac : a < c := by change a.val < a.val + 1; omega
  have hcb : c < b := by change a.val + 1 < b.val; omega
  have h1 := (s.orderEmbOfFin hs).strictMono hac
  have h2 := (s.orderEmbOfFin hs).strictMono hcb
  change (s.orderEmbOfFin hs a).val < (s.orderEmbOfFin hs c).val at h1
  change (s.orderEmbOfFin hs c).val < (s.orderEmbOfFin hs b).val at h2
  omega

theorem orderEmbOfFin_rank_zero {k : ℕ} (s : Finset (Fin N)) (hs : s.card = k)
    (a : Fin k) (hv : (s.orderEmbOfFin hs a).val = 0) : a.val = 0 := by
  by_contra hne
  let b : Fin k := ⟨0, by omega⟩
  have hb : b < a := by change 0 < a.val; omega
  have hp := (s.orderEmbOfFin hs).strictMono hb
  change (s.orderEmbOfFin hs b).val < (s.orderEmbOfFin hs a).val at hp
  omega

theorem orderEmbOfFin_rank_last {k : ℕ} (s : Finset (Fin N)) (hs : s.card = k)
    (a : Fin k) (hv : (s.orderEmbOfFin hs a).val + 1 = N) : a.val + 1 = k := by
  by_contra hne
  let b : Fin k := ⟨a.val + 1, by omega⟩
  have hb : a < b := by change a.val < a.val + 1; omega
  have hp := (s.orderEmbOfFin hs).strictMono hb
  change (s.orderEmbOfFin hs a).val < (s.orderEmbOfFin hs b).val at hp
  have hl := (s.orderEmbOfFin hs b).isLt
  omega

theorem nxt_val_wrap (i : Fin N) (hi : i.val + 1 = N) : (nxt i).val = 0 := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ k =>
    have he : i = Fin.last k := Fin.ext (by simp; omega)
    rw [he]
    exact congrArg Fin.val (finRotate_last (n := k))

/-- Every inadmissible choice has zero sine weight, including a collision across the seam. -/
theorem sineLiftWeight_inadmissible (hN : 2 ≤ N) (x : Finset (Fin N))
    (d : Fin (defects x).card → Bool)
    (ha : ¬ AdmissibleDefectChoice x (indexedDefectChoice x d)) :
    sineLiftWeight ((N : ℝ) + (defects x).card) (leftStepLift (orderedDefectLift x) d) = 0 := by
  unfold AdmissibleDefectChoice at ha
  push Not at ha
  obtain ⟨i, hj, hi, hnext⟩ := ha
  let e := (defects x).orderIsoOfFin rfl
  let a := e.symm i
  let b := e.symm ⟨nxt i.1, hj⟩
  have hav : (defects x).orderEmbOfFin rfl a = i.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply i)
  have hbv : (defects x).orderEmbOfFin rfl b = nxt i.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨nxt i.1, hj⟩)
  have hda : d a = false := hi
  have hdb : d b = true := by
    change d b ≠ false at hnext
    cases hh : d b <;> simp_all
  by_cases hwrap : i.1.val + 1 < N
  · have hnv := nxt_val_of_lt i.1 hwrap
    have hval : ((defects x).orderEmbOfFin rfl b).val =
        ((defects x).orderEmbOfFin rfl a).val + 1 := by rw [hav, hbv, hnv]
    have hrank := orderEmbOfFin_rank_succ (defects x) rfl a b hval
    have hab : a ≠ b := by intro he; rw [he] at hrank; omega
    apply sineLiftWeight_zero_of_equal _ _ hab
    simp only [leftStepLift, hda, hdb, Bool.false_eq_true, ↓reduceIte,
      orderedDefectLift, defectCoordinate, hav, hbv, hnv]
    omega
  · have hlast : i.1.val + 1 = N := by omega
    have hzero := nxt_val_wrap i.1 hlast
    have harank := orderEmbOfFin_rank_last (defects x) rfl a (by rw [hav]; exact hlast)
    have hbrank := orderEmbOfFin_rank_zero (defects x) rfl b (by rw [hbv]; exact hzero)
    have hab : b ≠ a := by
      intro he
      have heval := congrArg (fun j => ((defects x).orderEmbOfFin rfl j).val) he
      rw [hbv, hav, hzero] at heval
      omega
    have hp : (N + (defects x).card : ℤ) ≠ 0 := by omega
    have hdiff : leftStepLift (orderedDefectLift x) d a -
        leftStepLift (orderedDefectLift x) d b = (N + (defects x).card : ℤ) := by
      simp only [leftStepLift, hda, hdb, Bool.false_eq_true, ↓reduceIte,
        orderedDefectLift, defectCoordinate, hav, hbv, hzero]
      omega
    have hh := sineLiftWeight_zero_of_period_difference
      (N + (defects x).card : ℤ) hp (leftStepLift (orderedDefectLift x) d) hab hdiff
    simpa only [Int.cast_add, Int.cast_natCast] using hh

end PottsDiscontinuity.SixVertex
