module

public import PottsDiscontinuity.TorusRC.CrossingContracts
public import PottsDiscontinuity.TorusRC.MeasureFacts

/-! # Extracting an endpoint pair from the rectangle-crossing estimate -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- A rectangle crossing with the two horizontal endpoint coordinates fixed.
Impossible parity choices simply give an empty event. -/
def rectanglePairConnection (hNp : 0 < N) (hMp : 0 < M) (n : ℕ)
    (i j : Fin (3 * n + 1)) : Set (RCConfig N M) :=
  {A | ∃ u v : RotatedVertex,
    u.val = ((i.val : ℤ), 0) ∧ v.val = ((j.val : ℤ), (n : ℤ)) ∧
      ∃ w : (liftedStripGraph hNp hMp A 0 (3 * (n : ℤ))).Walk u v,
        ∀ z ∈ w.support, 0 ≤ z.val.2 ∧ z.val.2 ≤ (n : ℤ)}

theorem rectangleCrossing_covered_by_pairs (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (hn : 0 < n) (A : RCConfig N M)
    (hA : torusRCVerticalRectangleCrossing hNp hMp n A) :
    ∃ ij : Fin (3 * n + 1) × Fin (3 * n + 1),
      A ∈ rectanglePairConnection hNp hMp n ij.1 ij.2 := by
  obtain ⟨u,v,hu,hv,w,hw⟩ := hA
  have huv : u ≠ v := by
    intro h
    subst v
    omega
  have hend {a b : RotatedVertex}
      (p : (liftedStripGraph hNp hMp A 0 (3 * (n : ℤ))).Walk a b) (hab : a ≠ b) :
      0 ≤ a.val.1 ∧ a.val.1 ≤ 3 * (n : ℤ) := by
    cases p with
    | nil => exact (hab rfl).elim
    | cons hadj _ => exact hadj.2.2.1
  have hux := hend w huv
  have hvx := hend w.reverse huv.symm
  let i : Fin (3 * n + 1) := ⟨u.val.1.toNat, by omega⟩
  let j : Fin (3 * n + 1) := ⟨v.val.1.toNat, by omega⟩
  refine ⟨(i,j),u,v,?_,?_,w,hw⟩
  · apply Prod.ext <;> dsimp [i] <;> omega
  · apply Prod.ext <;> dsimp [j] <;> omega

/-- A finite union bound for the exact normalized indexed torus law. -/
theorem torusRCProbability_le_sum_of_cover {ι : Type*} [Fintype ι]
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) (F : ι → Set (RCConfig N M))
    (hcover : ∀ A ∈ E, ∃ i, A ∈ F i) :
    torusRCProbability hN hM q E ≤ ∑ i, torusRCProbability hN hM q (F i) := by
  classical
  rw [torusRCProbability_eq_sum]
  simp_rw [torusRCProbability_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A _
  have hnonneg : ∀ i, 0 ≤ (F i).indicator (torusRCMass hN hM q) A := by
    intro i
    by_cases hA : A ∈ F i <;> simp [Set.indicator, hA, (torusRCMass_pos hN hM q A).le]
  by_cases hA : A ∈ E
  · obtain ⟨i,hi⟩ := hcover A hA
    rw [Set.indicator_of_mem hA]
    calc
      _ = (F i).indicator (torusRCMass hN hM q) A := (Set.indicator_of_mem hi _).symm
      _ ≤ ∑ j, (F j).indicator (torusRCMass hN hM q) A :=
        Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  · rw [Set.indicator_of_notMem hA]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)

/-- The crossing lower bound supplies an actual pair, with the elementary
endpoint count (3n+1)^2. Its replacement by 16n^2 only changes the uniform
positive constant in the source's 9n^2 convention. -/
theorem rectanglePair_probability_ge (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ))
    (n : ℕ) (hn : 0 < n) (c : ℝ)
    (hc : c ≤ torusRCProbability hN hM q
      {A | torusRCVerticalRectangleCrossing hNp hMp n A}) :
    ∃ ij : Fin (3 * n + 1) × Fin (3 * n + 1),
      c / ((3 * (n : ℝ) + 1) ^ 2) ≤
        torusRCProbability hN hM q (rectanglePairConnection hNp hMp n ij.1 ij.2) := by
  classical
  let F := fun ij : Fin (3 * n + 1) × Fin (3 * n + 1) =>
    rectanglePairConnection hNp hMp n ij.1 ij.2
  have hsum := torusRCProbability_le_sum_of_cover hN hM q _ F
    (fun A hA => rectangleCrossing_covered_by_pairs hNp hMp n hn A hA)
  by_contra h
  push Not at h
  have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
    (fun i _ => h i)
  have heq : (∑ _ : Fin (3 * n + 1) × Fin (3 * n + 1),
      c / ((3 * (n : ℝ) + 1) ^ 2)) = c := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
  rw [heq] at hlt
  exact (not_lt_of_ge (hc.trans hsum)) hlt

/-- Point-pair extraction from the named crossing premise h319. The harmless
endpoint-count constant is absorbed into a new positive uniform constant,
retaining the source's exact 9n^2 denominator. -/
theorem point_pair_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N M n : ℕ) (hN : Even N) (hM : Even M)
      (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hn : 0 < n)
      (h3nN : 3 * n ≤ N) (h3nM : 3 * n ≤ M),
      let hNp : 0 < N := by omega
      let hMp : 0 < M := by omega
      ∃ ij : Fin (3 * n + 1) × Fin (3 * n + 1),
        c / (9 * (n : ℝ) ^ 2) ≤ torusRCProbability hN hM q
          (rectanglePairConnection hNp hMp n ij.1 ij.2) := by
  obtain ⟨c,hc,hcross⟩ := hh319
  refine ⟨c * 9 / 16, by positivity, ?_⟩
  intro N M n hN hM hN4 hM4 hn h3nN h3nM
  let hNp : 0 < N := by omega
  let hMp : 0 < M := by omega
  obtain ⟨ij,hij⟩ := rectanglePair_probability_ge hN hM hNp hMp q n hn c
    (hcross N M n hN hM hN4 hM4 hn h3nN h3nM)
  refine ⟨ij, ?_⟩
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (3 * (n : ℝ) + 1) ^ 2 ≤ 16 * (n : ℝ) ^ 2 := by nlinarith
  have hdiv : c / (16 * (n : ℝ) ^ 2) ≤ c / ((3 * (n : ℝ) + 1) ^ 2) :=
    div_le_div_of_nonneg_left hc.le (by positivity) hsq
  have heq : (c * 9 / 16) / (9 * (n : ℝ) ^ 2) = c / (16 * (n : ℝ) ^ 2) := by
    field_simp
  rw [heq]
  exact hdiv.trans hij

end PottsDiscontinuity.TorusRC
