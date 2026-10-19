module

public import PottsDiscontinuity.TorusRC.IndexedFK
public import PottsDiscontinuity.TorusRC.RectanglePairs

/-! # FKG association for the critical indexed torus law -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

def openIndexSet (A : RCConfig N M) : Finset (Fin N × Fin M) :=
  univ.filter fun v => A v = true

private theorem openIndexSet_inf (A B : RCConfig N M) :
    openIndexSet (A ⊓ B) = openIndexSet A ∩ openIndexSet B := by
  ext v
  simp only [openIndexSet, mem_filter, mem_univ, true_and, mem_inter]
  change (A v ⊓ B v = true) ↔ (A v = true ∧ B v = true)
  cases A v <;> cases B v <;> decide

private theorem openIndexSet_sup (A B : RCConfig N M) :
    openIndexSet (A ⊔ B) = openIndexSet A ∪ openIndexSet B := by
  ext v
  simp only [openIndexSet, mem_filter, mem_univ, true_and, mem_union]
  change (A v ⊔ B v = true) ↔ (A v = true ∨ B v = true)
  cases A v <;> cases B v <;> decide

private theorem openCount_lattice (A B : RCConfig N M) :
    openCount (A ⊓ B) + openCount (A ⊔ B) = openCount A + openCount B := by
  unfold openCount
  change (openIndexSet (A ⊓ B)).card + (openIndexSet (A ⊔ B)).card =
    (openIndexSet A).card + (openIndexSet B).card
  rw [openIndexSet_inf, openIndexSet_sup, card_inter_add_card_union]

private theorem closedCount_lattice (A B : RCConfig N M) :
    closedCount (A ⊓ B) + closedCount (A ⊔ B) = closedCount A + closedCount B := by
  have hA := openCount_add_closedCount A
  have hB := openCount_add_closedCount B
  have hi := openCount_add_closedCount (A ⊓ B)
  have hu := openCount_add_closedCount (A ⊔ B)
  have ho := openCount_lattice A B
  omega

theorem torusRCWeight_lattice_condition (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A B : RCConfig N M) :
    torusRCWeight hN hM q A * torusRCWeight hN hM q B ≤
      torusRCWeight hN hM q (A ⊓ B) * torusRCWeight hN hM q (A ⊔ B) := by
  let p : ℝ := (rcCriticalParameter q).val
  have hprod (C D : RCConfig N M) :
      torusRCWeight hN hM q C * torusRCWeight hN hM q D =
        (p ^ (openCount C + openCount D) *
          (1 - p) ^ (closedCount C + closedCount D)) *
            q.val ^ (clusterCount hN hM true C + clusterCount hN hM true D) := by
    have hp : (rcCriticalParameter q).val = p := rfl
    simp only [torusRCWeight, hp, pow_add]
    ring
  rw [hprod A B, hprod (A ⊓ B) (A ⊔ B), ← openCount_lattice A B,
    ← closedCount_lattice A B]
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_right₀ q.property (clusterCount_supermodular hN hM A B)
  · exact mul_nonneg (pow_nonneg (criticalParameter_pos q).le _)
      (pow_nonneg (sub_nonneg.mpr (criticalParameter_lt_one q).le) _)

theorem torusRCMass_lattice_condition (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A B : RCConfig N M) :
    torusRCMass hN hM q A * torusRCMass hN hM q B ≤
      torusRCMass hN hM q (A ⊓ B) * torusRCMass hN hM q (A ⊔ B) := by
  simp only [torusRCMass]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right
    (mul_pos (torusRCPartition_pos hN hM q) (torusRCPartition_pos hN hM q))).2
      (torusRCWeight_lattice_condition hN hM q A B)

/-- Increasing nonnegative functions are positively associated under the torus law. -/
theorem torusRC_positive_association (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (f g : RCConfig N M → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ A, torusRCMass hN hM q A * f A) *
      (∑ A, torusRCMass hN hM q A * g A) ≤
        ∑ A, torusRCMass hN hM q A * (f A * g A) := by
  classical
  have h := _root_.fkg (μ := torusRCMass hN hM q) (f := f) (g := g)
    (fun A => (torusRCMass_pos hN hM q A).le) hf0 hg0 hf hg
    (torusRCMass_lattice_condition hN hM q)
  simpa only [sum_torusRCMass, one_mul] using h

/-- Increasing events are positively associated under the normalized torus law. -/
theorem torusRCProbability_inter_ge_mul (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E F : Set (RCConfig N M))
    (hE : ∀ ⦃A B⦄, A ≤ B → A ∈ E → B ∈ E)
    (hF : ∀ ⦃A B⦄, A ≤ B → A ∈ F → B ∈ F) :
    torusRCProbability hN hM q E * torusRCProbability hN hM q F ≤
      torusRCProbability hN hM q (E ∩ F) := by
  classical
  let f : RCConfig N M → ℝ := fun A => if A ∈ E then 1 else 0
  let g : RCConfig N M → ℝ := fun A => if A ∈ F then 1 else 0
  have hf0 : ∀ A, 0 ≤ f A := by
    intro A
    unfold f
    split_ifs <;> norm_num
  have hg0 : ∀ A, 0 ≤ g A := by
    intro A
    unfold g
    split_ifs <;> norm_num
  have hf : Monotone f := by
    intro A B hAB
    by_cases hA : A ∈ E
    · have hB : B ∈ E := hE hAB hA
      simp [f, hA, hB]
    · have hfA : f A = 0 := by simp [f, hA]
      rw [hfA]
      by_cases hB : B ∈ E
      · have hfB : f B = 1 := by simp [f, hB]
        rw [hfB]
        norm_num
      · have hfB : f B = 0 := by simp [f, hB]
        rw [hfB]
  have hg : Monotone g := by
    intro A B hAB
    by_cases hA : A ∈ F
    · have hB : B ∈ F := hF hAB hA
      simp [g, hA, hB]
    · have hgA : g A = 0 := by simp [g, hA]
      rw [hgA]
      by_cases hB : B ∈ F
      · have hgB : g B = 1 := by simp [g, hB]
        rw [hgB]
        norm_num
      · have hgB : g B = 0 := by simp [g, hB]
        rw [hgB]
  have hassoc := torusRC_positive_association hN hM q f g hf0 hg0 hf hg
  have hleft : (∑ A, torusRCMass hN hM q A * f A) =
      torusRCProbability hN hM q E := by
    rw [torusRCProbability_eq_sum]
    apply Finset.sum_congr rfl
    intro A _
    by_cases hA : A ∈ E <;> simp [f, hA, Set.indicator]
  have hmiddle : (∑ A, torusRCMass hN hM q A * g A) =
      torusRCProbability hN hM q F := by
    rw [torusRCProbability_eq_sum]
    apply Finset.sum_congr rfl
    intro A _
    by_cases hA : A ∈ F <;> simp [g, hA, Set.indicator]
  have hright : (∑ A, torusRCMass hN hM q A * (f A * g A)) =
      torusRCProbability hN hM q (E ∩ F) := by
    rw [torusRCProbability_eq_sum]
    apply Finset.sum_congr rfl
    intro A _
    by_cases hE' : A ∈ E <;> by_cases hF' : A ∈ F <;>
      simp [f, g, hE', hF', Set.indicator, Set.mem_inter_iff]
  rw [← hleft, ← hmiddle, ← hright]
  exact hassoc

/-- A finite intersection of increasing torus events has probability at least
the product of the individual probabilities. -/
theorem torusRCProbability_finset_inter_ge_prod
    {ι : Type*} [DecidableEq ι] (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (s : Finset ι)
    (E : ι → Set (RCConfig N M))
    (hE : ∀ i ⦃A B⦄, A ≤ B → A ∈ E i → B ∈ E i) :
    (∏ i ∈ s, torusRCProbability hN hM q (E i)) ≤
      torusRCProbability hN hM q {A | ∀ i ∈ s, A ∈ E i} := by
  classical
  let F (t : Finset ι) : Set (RCConfig N M) := {A | ∀ i ∈ t, A ∈ E i}
  have hFmono (t : Finset ι) : ∀ ⦃A B⦄, A ≤ B → A ∈ F t → B ∈ F t := by
    intro A B hAB hA i hi
    exact hE i hAB (hA i hi)
  induction s using Finset.induction_on with
  | empty =>
      simp [torusRCProbability_univ]
  | @insert a s ha ih =>
      have hEq : F (insert a s) = F s ∩ E a := by
        ext A
        constructor
        · intro hA
          constructor
          · intro i hi
            exact hA i (Finset.mem_insert_of_mem hi)
          · exact hA a (Finset.mem_insert_self a s)
        · rintro ⟨hA, haA⟩ i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact haA
          · exact hA i hi
      have hstep := torusRCProbability_inter_ge_mul hN hM q (F s) (E a)
        (hFmono s) (hE a)
      calc
        (∏ i ∈ insert a s, torusRCProbability hN hM q (E i)) =
            (∏ i ∈ s, torusRCProbability hN hM q (E i)) *
              torusRCProbability hN hM q (E a) := by
                rw [Finset.prod_insert ha]
                ring
        _ ≤ torusRCProbability hN hM q (F s) *
              torusRCProbability hN hM q (E a) :=
                mul_le_mul_of_nonneg_right ih
                  (torusRCProbability_nonneg hN hM q (E a))
        _ ≤ torusRCProbability hN hM q (F s ∩ E a) := hstep
        _ = torusRCProbability hN hM q (F (insert a s)) := by rw [hEq]

end PottsDiscontinuity.TorusRC
