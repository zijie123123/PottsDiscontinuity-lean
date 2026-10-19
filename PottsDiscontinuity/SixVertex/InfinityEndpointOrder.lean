module

public import PottsDiscontinuity.SixVertex.InfinityLiftedChoices

/-! # Integer endpoint lifts of admissible defect choices -/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

@[simp] theorem indexedDefectChoice_ordered (x : Finset (Fin N))
    (d : Fin (defects x).card → Bool) (a : Fin (defects x).card) :
    indexedDefectChoice x d
      ⟨(defects x).orderEmbOfFin rfl a, (defects x).orderEmbOfFin_mem rfl a⟩ = d a := by
  change d ((defects x).orderIsoOfFin rfl |>.symm ((defects x).orderIsoOfFin rfl a)) = d a
  rw [OrderIso.symm_apply_apply]

/-- Cyclic finite endpoint of the indexed left/right move. -/
noncomputable def choiceEndpoint (x : Finset (Fin N))
    (d : Fin (defects x).card → Bool) (a : Fin (defects x).card) : Fin N :=
  if d a then prv ((defects x).orderEmbOfFin rfl a) else nxt ((defects x).orderEmbOfFin rfl a)

/-- Integer endpoint before sorting or cyclic reduction. -/
noncomputable def choiceEndpointLift (x : Finset (Fin N))
    (d : Fin (defects x).card → Bool) (a : Fin (defects x).card) : ℤ :=
  (((defects x).orderEmbOfFin rfl a).val : ℤ) + if d a then -1 else 1

theorem leftStepLift_eq_endpointLift (x : Finset (Fin N))
    (d : Fin (defects x).card → Bool) :
    leftStepLift (orderedDefectLift x) d = fun a => choiceEndpointLift x d a + a.val := by
  funext a
  simp only [leftStepLift, orderedDefectLift, defectCoordinate, choiceEndpointLift,
    Nat.cast_add]
  ring

theorem choiceEndpoint_eq_motion (x : Finset (Fin N)) (d : Fin (defects x).card → Bool)
    (a : Fin (defects x).card) :
    choiceEndpoint x d a = defectMotion (horizontalOfDefectChoice x (indexedDefectChoice x d))
      ((defects x).orderEmbOfFin rfl a) := by
  have hh := horizontalOfDefectChoice_prv x (indexedDefectChoice x d)
    ⟨(defects x).orderEmbOfFin rfl a, (defects x).orderEmbOfFin_mem rfl a⟩
  rw [indexedDefectChoice_ordered] at hh
  simp only [choiceEndpoint, defectMotion, hh]

/-- The local admissibility condition on two canonically indexed neighboring defects. -/
theorem admissible_indexed_succ (x : Finset (Fin N)) (d : Fin (defects x).card → Bool)
    (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
    (a b : Fin (defects x).card)
    (hab : nxt ((defects x).orderEmbOfFin rfl a) = (defects x).orderEmbOfFin rfl b) :
    d a = false → d b = false := by
  intro hh
  have hmem : nxt ((defects x).orderEmbOfFin rfl a) ∈ defects x := by
    rw [hab]
    exact (defects x).orderEmbOfFin_mem rfl b
  have hh' : indexedDefectChoice x d
      ⟨(defects x).orderEmbOfFin rfl a, (defects x).orderEmbOfFin_mem rfl a⟩ = false := by
    rw [indexedDefectChoice_ordered]
    exact hh
  have hc := ha ⟨(defects x).orderEmbOfFin rfl a, (defects x).orderEmbOfFin_mem rfl a⟩ hmem hh'
  have he : (⟨nxt ((defects x).orderEmbOfFin rfl a), hmem⟩ : DefectSite x) =
      ⟨(defects x).orderEmbOfFin rfl b, (defects x).orderEmbOfFin_mem rfl b⟩ := Subtype.ext hab
  rw [he, indexedDefectChoice_ordered] at hc
  exact hc

/-- Actual finite endpoints are injective for every admissible choice. -/
theorem choiceEndpoint_injective {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d)) :
    Function.Injective (choiceEndpoint x d) := by
  have hf := flux_horizontalOfDefectChoice hx (indexedDefectChoice x d) ha
  have hd := disjoint_upperOfDefectChoice hx (indexedDefectChoice x d)
  intro a b hab
  apply (defects x).orderEmbOfFin rfl |>.injective
  apply hf.defectMotion_injective hd ((defects x).orderEmbOfFin_mem rfl a)
    ((defects x).orderEmbOfFin_mem rfl b)
  simpa only [← choiceEndpoint_eq_motion] using hab

/-- Endpoint membership in the actual upper defect set. -/
theorem choiceEndpoint_mem {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
    (a : Fin (defects x).card) :
    choiceEndpoint x d a ∈ defects (upperOfHorizontal (horizontalOfDefectChoice x (indexedDefectChoice x d))) := by
  have hf := flux_horizontalOfDefectChoice hx (indexedDefectChoice x d) ha
  have hd := disjoint_upperOfDefectChoice hx (indexedDefectChoice x d)
  rw [hf.defects_eq_image hd]
  exact mem_image.mpr ⟨_, (defects x).orderEmbOfFin_mem rfl a, (choiceEndpoint_eq_motion x d a).symm⟩

theorem card_upper_defects_choice {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d)) :
    (defects (upperOfHorizontal (horizontalOfDefectChoice x (indexedDefectChoice x d)))).card =
      (defects x).card := by
  have hf := flux_horizontalOfDefectChoice hx (indexedDefectChoice x d) ha
  have hd := disjoint_upperOfDefectChoice hx (indexedDefectChoice x d)
  rw [hf.defects_eq_image hd]
  exact card_image_of_injOn (hf.defectMotion_injective hd)

theorem prv_val_zero (i : Fin N) (hi : i.val = 0) : (prv i).val + 1 = N := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ k =>
    have he : i = 0 := Fin.ext hi
    rw [he, prv_zero]
    simp

theorem choiceEndpointLift_bounds (x : Finset (Fin N)) (d : Fin (defects x).card → Bool)
    (a : Fin (defects x).card) : -1 ≤ choiceEndpointLift x d a ∧ choiceEndpointLift x d a ≤ N := by
  have hh := ((defects x).orderEmbOfFin rfl a).isLt
  unfold choiceEndpointLift
  cases hd : d a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Exact cyclic reduction of the integer endpoint, with both seam branches explicit. -/
theorem choiceEndpoint_val (x : Finset (Fin N)) (d : Fin (defects x).card → Bool)
    (a : Fin (defects x).card) :
    ((choiceEndpoint x d a).val : ℤ) =
      if choiceEndpointLift x d a < 0 then choiceEndpointLift x d a + N
      else if (N : ℤ) ≤ choiceEndpointLift x d a then choiceEndpointLift x d a - N
      else choiceEndpointLift x d a := by
  let i := (defects x).orderEmbOfFin rfl a
  have hi := i.isLt
  cases hd : d a
  · by_cases hn : i.val + 1 < N
    · have hn' := nxt_val_of_lt i hn
      simp only [choiceEndpoint, choiceEndpointLift, hd, Bool.false_eq_true, ↓reduceIte]
      change ((nxt i).val : ℤ) = _
      rw [hn']
      split_ifs <;> omega
    · have hn' := nxt_val_wrap i (by omega)
      simp only [choiceEndpoint, choiceEndpointLift, hd, Bool.false_eq_true, ↓reduceIte]
      change ((nxt i).val : ℤ) = _
      rw [hn']
      split_ifs <;> omega
  · by_cases hz : i.val = 0
    · have hp := prv_val_zero i hz
      simp only [choiceEndpoint, choiceEndpointLift, hd, ↓reduceIte]
      change ((prv i).val : ℤ) = _
      split_ifs <;> omega
    · have hp := prv_val_of_pos i (by omega)
      simp only [choiceEndpoint, choiceEndpointLift, hd, ↓reduceIte]
      change ((prv i).val : ℤ) = _
      rw [hp]
      split_ifs <;> omega

theorem choiceEndpointLift_injective {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d)) :
    Function.Injective (choiceEndpointLift x d) := by
  intro a b hab
  have h1 := choiceEndpoint_val x d a
  have h2 := choiceEndpoint_val x d b
  rw [hab] at h1
  have h3 : ((choiceEndpoint x d a).val : ℤ) = (choiceEndpoint x d b).val := h1.trans h2.symm
  apply choiceEndpoint_injective hx d ha
  apply Fin.ext
  exact_mod_cast h3

/-- Valid integer endpoint lifts preserve the strict linear order before reducing modulo N. -/
theorem choiceEndpointLift_strictMono {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d)) :
    StrictMono (choiceEndpointLift x d) := by
  intro a b hab
  have hsite := (defects x).orderEmbOfFin rfl |>.strictMono hab
  change ((defects x).orderEmbOfFin rfl a).val <
    ((defects x).orderEmbOfFin rfl b).val at hsite
  have hne : choiceEndpointLift x d a ≠ choiceEndpointLift x d b :=
    (choiceEndpointLift_injective hx d ha).ne (ne_of_lt hab)
  have hnoswap : ¬ (((defects x).orderEmbOfFin rfl b).val =
      ((defects x).orderEmbOfFin rfl a).val + 1 ∧ d a = false ∧ d b = true) := by
    rintro ⟨hv, hda, hdb⟩
    have hnext : nxt ((defects x).orderEmbOfFin rfl a) = (defects x).orderEmbOfFin rfl b := by
      apply Fin.ext
      have hb := ((defects x).orderEmbOfFin rfl b).isLt
      rw [nxt_val_of_lt _ (by omega)]
      exact hv.symm
    have hh := admissible_indexed_succ x d ha a b hnext hda
    rw [hdb] at hh
    contradiction
  cases hda : d a <;> cases hdb : d b <;>
    simp only [choiceEndpointLift, hda, hdb, Bool.false_eq_true, ↓reduceIte, and_true] at hne hnoswap ⊢ <;> omega

private theorem choiceEndpointLift_no_extremes {x : Finset (Fin N)}
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
    (a b : Fin (defects x).card) :
    ¬ (choiceEndpointLift x d a = -1 ∧ choiceEndpointLift x d b = N) := by
  rintro ⟨ha0, hbN⟩
  have hba := ((defects x).orderEmbOfFin rfl a).isLt
  have hbb := ((defects x).orderEmbOfFin rfl b).isLt
  have hda : d a = true := by
    cases hh : d a
    · simp only [choiceEndpointLift, hh, Bool.false_eq_true, ↓reduceIte] at ha0
      omega
    · rfl
  have hdb : d b = false := by
    cases hh : d b
    · rfl
    · simp only [choiceEndpointLift, hh, ↓reduceIte] at hbN
      omega
  have hval0 : ((defects x).orderEmbOfFin rfl a).val = 0 := by
    simp only [choiceEndpointLift, hda, ↓reduceIte] at ha0
    omega
  have hvalN : ((defects x).orderEmbOfFin rfl b).val + 1 = N := by
    simp only [choiceEndpointLift, hdb, Bool.false_eq_true, ↓reduceIte] at hbN
    omega
  have hnext : nxt ((defects x).orderEmbOfFin rfl b) = (defects x).orderEmbOfFin rfl a := by
    apply Fin.ext
    rw [nxt_val_wrap _ hvalN, hval0]
  have hh := admissible_indexed_succ x d ha b a hnext hdb
  rw [hda] at hh
  contradiction

/-- All endpoints remain in a cyclic interval of length strictly less than N. -/
theorem choiceEndpointLift_span {x : Finset (Fin N)} (hN : 0 < N) (hx : NoConsecutiveUp x)
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
    (a b : Fin (defects x).card) : choiceEndpointLift x d b - choiceEndpointLift x d a < N := by
  have h1 := choiceEndpointLift_bounds x d a
  have h2 := choiceEndpointLift_bounds x d b
  have hnot := choiceEndpointLift_no_extremes d ha a b
  have hne : choiceEndpointLift x d b - choiceEndpointLift x d a ≠ N := by
    intro he
    have hfa := choiceEndpoint_val x d a
    have hfb := choiceEndpoint_val x d b
    have hvals : ((choiceEndpoint x d a).val : ℤ) = (choiceEndpoint x d b).val := by
      split_ifs at hfa hfb <;> omega
    have hab : a = b := choiceEndpoint_injective hx d ha (Fin.ext (by exact_mod_cast hvals))
    subst b
    omega
  omega

end PottsDiscontinuity.SixVertex
