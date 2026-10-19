module

public import PottsDiscontinuity.TorusRC.Measure

/-! # Finite-event formulas for the indexed torus probability -/

@[expose] public section

open MeasureTheory Finset

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

theorem torusRCProbability_eq_sum (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q E = ∑ A, E.indicator (torusRCMass hN hM q) A := by
  classical
  have hn (A : RCConfig N M) : 0 ≤ E.indicator (torusRCMass hN hM q) A := by
    by_cases h : A ∈ E <;> simp only [Set.indicator, h, ite_true, ite_false]
    · exact (torusRCMass_pos hN hM q A).le
    · exact le_rfl
  have he : torusRCMeasure hN hM q E =
      ENNReal.ofReal (∑ A, E.indicator (torusRCMass hN hM q) A) := by
    rw [torusRCMeasure, PMF.toMeasure_apply_fintype,
      ENNReal.ofReal_sum_of_nonneg (fun A _ => hn A)]
    apply sum_congr rfl
    intro A _
    by_cases h : A ∈ E <;> simp [h, torusRCPMF_apply]
  unfold torusRCProbability Measure.real
  rw [he, ENNReal.toReal_ofReal (sum_nonneg (fun A _ => hn A))]

theorem torusRCProbability_nonneg (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    0 ≤ torusRCProbability hN hM q E := ENNReal.toReal_nonneg

theorem torusRCProbability_le_one (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q E ≤ 1 := by
  exact measureReal_le_one

theorem torusRCProbability_mono (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) {E F : Set (RCConfig N M)} (hEF : E ⊆ F) :
    torusRCProbability hN hM q E ≤ torusRCProbability hN hM q F := by
  exact measureReal_mono hEF

@[simp] theorem torusRCProbability_univ (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : torusRCProbability hN hM q Set.univ = 1 := by
  rw [torusRCProbability_eq_sum]
  simp only [Set.indicator_univ, sum_torusRCMass]

@[simp] theorem torusRCProbability_empty (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) : torusRCProbability hN hM q ∅ = 0 := by
  rw [torusRCProbability_eq_sum]
  simp only [Set.indicator_empty, sum_const_zero]

theorem torusRCProbability_pos_iff (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    0 < torusRCProbability hN hM q E ↔ E.Nonempty := by
  constructor
  · intro h
    by_contra he
    have : E = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    rw [this, torusRCProbability_empty] at h
    exact (lt_irrefl 0) h
  · rintro ⟨A, hA⟩
    have hs : {A} ⊆ E := Set.singleton_subset_iff.mpr hA
    have hm := torusRCProbability_mono hN hM q hs
    rw [torusRCProbability_singleton] at hm
    exact (torusRCMass_pos hN hM q A).trans_le hm

end PottsDiscontinuity.TorusRC
