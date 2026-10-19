module

public import PottsDiscontinuity.TorusTopology.PeriodicCurveBasics
public import PottsDiscontinuity.TorusTopology.UpperReturnGeometry
public import PottsDiscontinuity.TorusTopology.CompassWordTurning

/-! Supporting phases and finite sums for an actual periodic lattice curve. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Finset

lemma periodic_translation_supporting_phase (f : ℕ → ℤ × ℤ) (L : ℕ) (D : ℤ × ℤ)
    (hL : 0 < L) (hp : ∀ n, f (n+L)=f n+D) :
    ∃ k < L, ∀ n, deckNormalHeight D (f n) ≤ deckNormalHeight D (f k) := by
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image (range L) (fun n => deckNormalHeight D (f n))
    ⟨0,mem_range.mpr hL⟩
  refine ⟨k,mem_range.mp hk,?_⟩
  intro n
  rw [periodic_translation_decompose f L D hp n,deckNormalHeight_add_deck]
  exact hmax (n%L) (mem_range.mpr (Nat.mod_lt n hL))

lemma periodic_translation_mul (f : ℕ → ℤ × ℤ) (L : ℕ) (D : ℤ × ℤ)
    (hp : ∀ n, f (n+L)=f n+D) (k : ℕ) :
    f (k*L) = f 0+k • D := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul,hp,ih,add_nsmul]
    simp only [one_nsmul]
    abel

lemma sum_periodic_shift (t : ℕ → ℤ) (L : ℕ) (ht : ∀ n, t (n+L)=t n) (n : ℕ) :
    (∑ k ∈ range L, t (n+k)) = ∑ k ∈ range L, t k := by
  have h₁ := Finset.sum_range_add t n L
  have h₂ := Finset.sum_range_add t L n
  have hh : (∑ k ∈ range n, t (L+k)) = ∑ k ∈ range n, t k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_comm,ht]
  rw [hh,Nat.add_comm L n] at h₂
  omega

lemma sum_periodic_mul (t : ℕ → ℤ) (L : ℕ) (ht : ∀ n, t (n+L)=t n) (r : ℕ) :
    (∑ k ∈ range (r*L), t k) = (r : ℤ) * ∑ k ∈ range L, t k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih,sum_periodic_shift t L ht]
    push_cast
    ring

lemma compassWordCyclicTurn_range (a : ℕ → Fin 4) (L : ℕ) (hL : 0 < L)
    (ha : a L = a 0) :
    compassWordCyclicTurn ((List.range L).map a) =
      ∑ k ∈ range L, Planar.Medial.primalCompassQuarterTurn (a k) (a (k+1)) := by
  unfold compassWordCyclicTurn
  rw [rotate_range_map_one a L hL ha,List.zipWith_map,List.zipWith_self]
  have hsum (t : ℕ → ℤ) (n : ℕ) :
      ((List.range n).map t).sum = ∑ k ∈ range n, t k := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]
  exact hsum _ _

end PottsDiscontinuity.TorusTopology
