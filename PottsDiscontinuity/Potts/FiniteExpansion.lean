module

public import PottsDiscontinuity.Potts.Parameters

/-!
# Finite Edwards–Sokal weight expansion

This finite algebra applies to any list of spin agreement constraints. An open
bond enforces its constraint; a closed bond has weight `exp (-β)`. The two
marginal computations below are proved by finite sums, without a coupling
assumption. The graph and literal boundary identifications are separate steps.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

variable {E S : Type*} [Fintype E]

/-- A single Edwards–Sokal bond factor. -/
def bondFactor (β : ℝ) (P : Prop) (b : Bool) : ℝ :=
  if b then (if P then bondProbability β else 0) else Real.exp (-β)

/-- The joint unnormalized weight of spins and bonds. -/
def constraintJointWeight (β : ℝ) (sat : S → E → Prop) (σ : S) (ω : E → Bool) : ℝ :=
  ∏ e, bondFactor β (sat σ e) (ω e)

/-- The Gibbs weight for the supplied agreement constraints. -/
def constraintGibbsWeight (β : ℝ) (sat : S → E → Prop) (σ : S) : ℝ :=
  Real.exp (β * ∑ e, if sat σ e then (1 : ℝ) else 0)

/-- The Bernoulli part of the bond weight, before the cluster-colouring count. -/
def bernoulliBondWeight (β : ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, if ω e then bondProbability β else Real.exp (-β)

theorem sum_bondFactor (β : ℝ) (P : Prop) :
    ∑ b : Bool, bondFactor β P b =
      Real.exp (-β) * Real.exp (β * if P then 1 else 0) := by
  by_cases h : P
  · simp only [Fintype.sum_bool, bondFactor, Bool.false_eq_true, ↓reduceIte, h,
      mul_one, bondProbability]
    rw [← Real.exp_add]
    simp
  · simp [bondFactor, h]

theorem sum_constraintJointWeight_bonds (β : ℝ) (sat : S → E → Prop) (σ : S) :
    ∑ ω : E → Bool, constraintJointWeight β sat σ ω =
      Real.exp (-β) ^ Fintype.card E * constraintGibbsWeight β sat σ := by
  unfold constraintJointWeight
  rw [← Fintype.prod_sum]
  simp_rw [sum_bondFactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.exp_sum, ← Finset.mul_sum]
  rfl

theorem constraintJointWeight_eq (β : ℝ) (sat : S → E → Prop)
    (σ : S) (ω : E → Bool) :
    constraintJointWeight β sat σ ω = bernoulliBondWeight β ω *
      (if ∀ e, ω e = true → sat σ e then 1 else 0) := by
  have h (e : E) : bondFactor β (sat σ e) (ω e) =
      (if ω e then bondProbability β else Real.exp (-β)) *
        (if ω e = true → sat σ e then 1 else 0) := by
    cases ω e <;> by_cases hs : sat σ e <;> simp [bondFactor, hs]
  simp only [constraintJointWeight, h, Finset.prod_mul_distrib,
    Fintype.prod_boole, bernoulliBondWeight]

theorem bernoulliBondWeight_eq (β : ℝ) (ω : E → Bool) :
    bernoulliBondWeight β ω = bondProbability β ^ Nat.card {e // ω e = true} *
      (1 - bondProbability β) ^ Nat.card {e // ω e = false} := by
  simp only [bernoulliBondWeight, Finset.prod_ite, Finset.prod_const,
    Nat.card_eq_fintype_card, Fintype.card_subtype, one_sub_bondProbability,
    Bool.not_eq_true]

variable [Fintype S]

/-- The bond marginal counts exactly the spin configurations compatible with
its open constraints. For graph constraints this count is a power of `q`. -/
theorem sum_constraintJointWeight_spins (β : ℝ) (sat : S → E → Prop) (ω : E → Bool) :
    ∑ σ : S, constraintJointWeight β sat σ ω =
      bernoulliBondWeight β ω * Nat.card {σ : S // ∀ e, ω e = true → sat σ e} := by
  simp only [constraintJointWeight_eq, ← Finset.mul_sum, Finset.sum_boole,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The partition function of the joint spin-bond weight. -/
def constraintJointPartition (β : ℝ) (sat : S → E → Prop) : ℝ :=
  ∑ σ : S, ∑ ω : E → Bool, constraintJointWeight β sat σ ω

theorem constraintJointPartition_eq (β : ℝ) (sat : S → E → Prop) :
    constraintJointPartition β sat = Real.exp (-β) ^ Fintype.card E *
      ∑ σ : S, constraintGibbsWeight β sat σ := by
  simp only [constraintJointPartition, sum_constraintJointWeight_bonds, Finset.mul_sum]

theorem constraintJointPartition_pos [Nonempty S] (β : ℝ) (sat : S → E → Prop) :
    0 < constraintJointPartition β sat := by
  rw [constraintJointPartition_eq]
  apply mul_pos (pow_pos (Real.exp_pos _) _)
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The normalized joint spin-bond probability mass. -/
def constraintJointProbability (β : ℝ) (sat : S → E → Prop)
    (σ : S) (ω : E → Bool) : ℝ :=
  constraintJointWeight β sat σ ω / constraintJointPartition β sat

theorem constraintJointProbability_nonneg [Nonempty S] {β : ℝ} (hβ : 0 < β)
    (sat : S → E → Prop) (σ : S) (ω : E → Bool) :
    0 ≤ constraintJointProbability β sat σ ω := by
  apply div_nonneg _ (constraintJointPartition_pos β sat).le
  apply Finset.prod_nonneg
  intro e _
  unfold bondFactor
  split_ifs
  · exact (bondProbability_pos hβ).le
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem sum_constraintJointProbability [Nonempty S] (β : ℝ) (sat : S → E → Prop) :
    ∑ σ : S, ∑ ω : E → Bool, constraintJointProbability β sat σ ω = 1 := by
  simp only [constraintJointProbability, ← Finset.sum_div]
  exact div_self (constraintJointPartition_pos β sat).ne'

/-- Exact Gibbs spin marginal of the finite joint law. -/
theorem constraintJointProbability_spin_marginal [Nonempty S]
    (β : ℝ) (sat : S → E → Prop) (σ : S) :
    ∑ ω : E → Bool, constraintJointProbability β sat σ ω =
      constraintGibbsWeight β sat σ / ∑ τ : S, constraintGibbsWeight β sat τ := by
  simp only [constraintJointProbability, ← Finset.sum_div,
    sum_constraintJointWeight_bonds, constraintJointPartition_eq]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Real.exp_ne_zero _))

end

end PottsDiscontinuity.Potts
