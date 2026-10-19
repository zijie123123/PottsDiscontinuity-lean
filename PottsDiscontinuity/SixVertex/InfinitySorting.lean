module

public import PottsDiscontinuity.SixVertex.InfinityCyclic
public import PottsDiscontinuity.SixVertex.InfinityGround

/-! # Canonical ordering of moved cyclic defect lifts -/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N k : ℕ}

/-- Shift an ordered site's integer coordinate by its label. -/
noncomputable def orderedSiteLift (s : Finset (Fin N)) (hs : s.card = k) : Fin k → ℤ :=
  fun a => ((s.orderEmbOfFin hs a).val : ℤ) + a.val

theorem defectGroundWeight_eq_orderedSiteLift (x : Finset (Fin N)) (hs : (defects x).card = k) :
    defectGroundWeight x = sineLiftWeight ((N : ℝ) + k) (orderedSiteLift (defects x) hs) := by
  subst k
  simp only [defectGroundWeight, sineLiftWeight, orderedSiteLift, defectCoordinate,
    Int.cast_add, Int.cast_natCast, Nat.cast_add]

private theorem strictMono_snoc {A : Type*} [Preorder A] {k : ℕ}
    {f : Fin k → A} {a : A} (hf : StrictMono f) (ha : ∀ i, f i < a) :
    StrictMono (Fin.snoc f a) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last => exact ((not_lt_of_ge (Fin.le_last j)) hij).elim
  | cast i =>
    cases j using Fin.lastCases with
    | last => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using ha i
    | cast j =>
      have hij' : i < j := hij
      simpa only [Fin.snoc_castSucc] using hf hij'

/-- With no seam crossing, the canonical ordered endpoint lift is the labelled lift. -/
theorem sineLiftWeight_canonical_no_wrap (s : Finset (Fin N)) (hs : s.card = k)
    (u : Fin k → ℤ) (hu : StrictMono u) (f : Fin k → Fin N)
    (hmem : ∀ a, f a ∈ s) (hf : ∀ a, ((f a).val : ℤ) = u a) :
    sineLiftWeight ((N : ℝ) + k) (orderedSiteLift s hs) =
      sineLiftWeight ((N : ℝ) + k) (fun a => u a + a.val) := by
  have hfm : StrictMono f := by
    intro a b hab
    have hh := hu hab
    rw [← hf a, ← hf b] at hh
    exact_mod_cast hh
  have he := Finset.orderEmbOfFin_unique hs hmem hfm
  have hcoord : orderedSiteLift s hs = fun a => u a + a.val := by
    funext a
    unfold orderedSiteLift
    rw [← congrFun he a, hf a]
  rw [hcoord]

/-- A left seam crossing moves the old first endpoint to the end. The label
change contributes a common translation by minus one, which cancels exactly. -/
theorem sineLiftWeight_canonical_left_wrap {k : ℕ} (hN : 0 < N)
    (s : Finset (Fin N)) (hs : s.card = k + 1) (u : Fin (k + 1) → ℤ)
    (hu : StrictMono u) (h0 : u 0 = -1) (f : Fin (k + 1) → Fin N)
    (hmem : ∀ a, f a ∈ s) (hf0 : ((f 0).val : ℤ) = N - 1)
    (hfs : ∀ a : Fin k, ((f a.succ).val : ℤ) = u a.succ)
    (hbound : ∀ a : Fin k, u a.succ < (N : ℤ) - 1) :
    sineLiftWeight ((N : ℝ) + ((k + 1 : ℕ) : ℝ)) (orderedSiteLift s hs) =
      sineLiftWeight ((N : ℝ) + ((k + 1 : ℕ) : ℝ)) (fun a => u a + a.val) := by
  let g : Fin (k + 1) → Fin N := Fin.snoc (fun a : Fin k => f a.succ) (f 0)
  have hgm : StrictMono g := by
    apply strictMono_snoc
    · intro a b hab
      have hab' : a.succ < b.succ := by change a.val + 1 < b.val + 1; omega
      have hh := hu hab'
      rw [← hfs a, ← hfs b] at hh
      exact_mod_cast hh
    · intro a
      have hh := hbound a
      rw [← hf0, ← hfs a] at hh
      exact_mod_cast hh
  have hgmemb : ∀ a, g a ∈ s := by
    intro a
    cases a using Fin.lastCases with
    | last => simpa only [g, Fin.snoc_last] using hmem 0
    | cast a => simpa only [g, Fin.snoc_castSucc] using hmem a.succ
  have he := Finset.orderEmbOfFin_unique hs hgmemb hgm
  let P : ℤ := N + (k + 1)
  let t : Fin (k + 1) → ℤ := fun a => u a + a.val
  have hcoord : orderedSiteLift s hs = fun a => cyclicLiftLeft P t a + (-1) := by
    funext a
    unfold orderedSiteLift
    rw [← congrFun he a]
    cases a using Fin.lastCases with
    | cast a =>
      simp only [g, Fin.snoc_castSucc, cyclicLiftLeft, Fin.snoc_castSucc,
        t, Fin.val_succ, Fin.val_castSucc, hfs, Nat.cast_add, Nat.cast_one]
      ring
    | last =>
      simp only [g, Fin.snoc_last, cyclicLiftLeft, Fin.snoc_last, t, hf0, h0,
        Fin.val_zero, Fin.val_last, Nat.cast_zero, P]
      ring
  rw [hcoord, sineLiftWeight_translate]
  have hp : P ≠ 0 := by dsimp [P]; omega
  simpa only [P, t, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one] using
    sineLiftWeight_cyclicLiftLeft P hp t

/-- A right seam crossing puts the old last endpoint first. Applying the left
cyclic cut to the canonical lift differs from the original lift by translation one. -/
theorem sineLiftWeight_canonical_right_wrap {k : ℕ} (hN : 0 < N)
    (s : Finset (Fin N)) (hs : s.card = k + 1) (u : Fin (k + 1) → ℤ)
    (hu : StrictMono u) (hlast : u (Fin.last k) = N) (f : Fin (k + 1) → Fin N)
    (hmem : ∀ a, f a ∈ s) (hflast : ((f (Fin.last k)).val : ℤ) = 0)
    (hfs : ∀ a : Fin k, ((f a.castSucc).val : ℤ) = u a.castSucc)
    (hbound : ∀ a : Fin k, 0 < u a.castSucc) :
    sineLiftWeight ((N : ℝ) + ((k + 1 : ℕ) : ℝ)) (orderedSiteLift s hs) =
      sineLiftWeight ((N : ℝ) + ((k + 1 : ℕ) : ℝ)) (fun a => u a + a.val) := by
  let g : Fin (k + 1) → Fin N := Fin.cons (f (Fin.last k)) (fun a : Fin k => f a.castSucc)
  have hgm : StrictMono g := by
    apply Fin.strictMono_cons.mpr
    constructor
    · intro a
      have hh := hbound a
      rw [← hfs a, ← hflast] at hh
      exact_mod_cast hh
    · intro a b hab
      have hab' : a.castSucc < b.castSucc := hab
      have hh := hu hab'
      rw [← hfs a, ← hfs b] at hh
      exact_mod_cast hh
  have hgmemb : ∀ a, g a ∈ s := by
    intro a
    cases a using Fin.cases with
    | zero => exact hmem (Fin.last k)
    | succ a => exact hmem a.castSucc
  have he := Finset.orderEmbOfFin_unique hs hgmemb hgm
  let P : ℤ := N + (k + 1)
  let t : Fin (k + 1) → ℤ := fun a => u a + a.val
  have hcoord : cyclicLiftLeft P (orderedSiteLift s hs) = fun a => t a + 1 := by
    funext a
    cases a using Fin.lastCases with
    | cast a =>
      simp only [cyclicLiftLeft, Fin.snoc_castSucc, orderedSiteLift]
      rw [← congrFun he a.succ]
      simp only [g, Fin.cons_succ, hfs, t, Fin.val_succ, Fin.val_castSucc,
        Nat.cast_add, Nat.cast_one]
      ring
    | last =>
      simp only [cyclicLiftLeft, Fin.snoc_last, orderedSiteLift]
      rw [← congrFun he 0]
      simp only [g, Fin.cons_zero, hflast, t, hlast, Fin.val_zero, Fin.val_last,
        Nat.cast_zero, P]
      ring
  have hp : P ≠ 0 := by dsimp [P]; omega
  have hc := sineLiftWeight_cyclicLiftLeft P hp (orderedSiteLift s hs)
  rw [hcoord, sineLiftWeight_translate] at hc
  simpa only [P, t, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one] using hc.symm

end PottsDiscontinuity.SixVertex
