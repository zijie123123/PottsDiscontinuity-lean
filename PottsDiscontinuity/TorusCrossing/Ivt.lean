module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

/-!
# A discrete intermediate value property for paths

If a path moves the integer level `r` by at most one at each step, then a path from level `≤ c` to
level `≥ c + k` contains a sub-path from level `c` to level `c + k` staying in the levels
`[c, c + k]`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open Relation

variable {α : Type*} (R : α → α → Prop) (r : α → ℤ)

theorem ivt_lower (hstep : ∀ p q, R p q → r q ≤ r p + 1 ∧ r p ≤ r q + 1) (c : ℤ) {a b : α}
    (hab : ReflTransGen R a b) (ha : r a ≤ c) (hb : c ≤ r b) :
    ∃ x, r x = c ∧ ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b := by
  have hge : ∀ x b, r x = c →
      ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b → c ≤ r b := by
    intro x b hx hxb
    induction hxb with
    | refl => exact hx.ge
    | tail _ hstep _ => exact hstep.2.2
  have key : ∀ b, ReflTransGen R a b →
      r b < c ∨ ∃ x, r x = c ∧ ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b := by
    intro b hb
    induction hb with
    | refl =>
      by_cases h : r a < c
      · exact Or.inl h
      · exact Or.inr ⟨a, by omega, ReflTransGen.refl⟩
    | @tail b b' _ hbb' ih =>
      have hs := hstep b b' hbb'
      rcases ih with h | ⟨x, hx, hxb⟩
      · by_cases h' : r b' < c
        · exact Or.inl h'
        · exact Or.inr ⟨b', by omega, ReflTransGen.refl⟩
      · have hrb := hge x b hx hxb
        by_cases h' : r b' < c
        · exact Or.inl h'
        · exact Or.inr ⟨x, hx, hxb.tail ⟨hbb', hrb, by omega⟩⟩
  rcases key b hab with h | h
  · omega
  · exact h

theorem ivt_upper (hstep : ∀ p q, R p q → r q ≤ r p + 1 ∧ r p ≤ r q + 1) (c : ℤ) (k : ℕ) {x b : α}
    (hx : r x = c) (hxb : ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b)
    (hb : c + k ≤ r b) :
    ∃ y, r y = c + k ∧
      ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ r p ≤ c + k ∧ c ≤ r q ∧ r q ≤ c + k) x y := by
  have key : ∀ b, ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b →
      (r b ≤ c + k ∧ ReflTransGen
        (fun p q => R p q ∧ c ≤ r p ∧ r p ≤ c + k ∧ c ≤ r q ∧ r q ≤ c + k) x b) ∨
      ∃ y, r y = c + k ∧
        ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ r p ≤ c + k ∧ c ≤ r q ∧ r q ≤ c + k) x y := by
    intro b hb
    induction hb with
    | refl => exact Or.inl ⟨by omega, ReflTransGen.refl⟩
    | @tail b b' _ hbb' ih =>
      obtain ⟨hR, hcb, hcb'⟩ := hbb'
      have hs := hstep b b' hR
      rcases ih with ⟨hle, hpath⟩ | h
      · by_cases h' : r b' ≤ c + k
        · exact Or.inl ⟨h', hpath.tail ⟨hR, hcb, hle, hcb', h'⟩⟩
        · exact Or.inr ⟨b, by omega, hpath⟩
      · exact Or.inr h
  rcases key b hxb with ⟨hle, hpath⟩ | h
  · exact ⟨b, by omega, hpath⟩
  · exact h

theorem ivt_path (hstep : ∀ p q, R p q → r q ≤ r p + 1 ∧ r p ≤ r q + 1) (c : ℤ) (k : ℕ) {a b : α}
    (hab : ReflTransGen R a b) (ha : r a ≤ c) (hb : c + k ≤ r b) :
    ∃ x y, r x = c ∧ r y = c + k ∧
      ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ r p ≤ c + k ∧ c ≤ r q ∧ r q ≤ c + k) x y := by
  obtain ⟨x, hx, hxb⟩ := ivt_lower R r hstep c hab ha (by omega)
  obtain ⟨y, hy, hxy⟩ := ivt_upper R r hstep c k hx hxb hb
  exact ⟨x, y, hx, hy, hxy⟩

end PottsDiscontinuity.TorusCrossing
