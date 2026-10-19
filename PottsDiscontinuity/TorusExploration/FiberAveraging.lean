module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import PottsDiscontinuity.FK.Expectation

/-! Exact averaging of conditional laws along the fibers of a finite record.
Repeated records are harmless: their conditional laws are averaged against the
original law, with no representative choice. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK.FiniteProbability
noncomputable section
open scoped Classical
variable {α β : Type*} [Fintype α]

/-- The genuine conditional law given the record of a, for a full-support law. -/
def recordConditional (p : PMF α) (hp : ∀ a, a ∈ p.support) (f : α → β) (a : α) : PMF α :=
  p.filter {b | f b=f a} ⟨a,rfl,hp a⟩

lemma recordMass_ne_zero (p : PMF α) (hp : ∀ a, a ∈ p.support) (f : α → β) (a : α) :
    (∑ b : α, if f b=f a then p b else 0) ≠ 0 := by
  intro hz
  have ha : p a ≤ ∑ b : α, if f b=f a then p b else 0 := by
    simpa only [ite_true] using
      (Finset.single_le_sum (f := fun b : α => if f b=f a then p b else 0)
        (fun b _ => bot_le) (Finset.mem_univ a) :
        (if f a=f a then p a else 0) ≤ ∑ b : α, if f b=f a then p b else 0)
  exact hp a (le_zero_iff.mp (hz ▸ ha))

lemma recordMass_ne_top (p : PMF α) (f : α → β) (a : α) :
    (∑ b : α, if f b=f a then p b else 0) ≠ ⊤ := by
  have h := p.tsum_coe_indicator_ne_top {b | f b=f a}
  simpa only [tsum_fintype,Set.indicator_apply,Set.mem_ofPred_eq] using h

/-- The original law is the average of its conditional record laws, weighted
by the original samples. -/
theorem bind_recordConditional (p : PMF α) (hp : ∀ a, a ∈ p.support) (f : α → β) :
    p.bind (recordConditional p hp f) = p := by
  ext b
  rw [PMF.bind_apply,tsum_fintype]
  have he (a : α) : p a * recordConditional p hp f a b =
      (if f a=f b then p a else 0) *
        (p b * (∑ c : α, if f c=f b then p c else 0)⁻¹) := by
    rw [recordConditional,PMF.filter_apply,tsum_fintype]
    by_cases h : f a=f b
    · have hfib : {c : α | f c=f a} = {c | f c=f b} := by rw [h]
      rw [hfib]
      simp only [Set.indicator_apply,Set.mem_ofPred_eq,h,eq_self,ite_true]
    · have h' : f b ≠ f a := Ne.symm h
      simp only [Set.indicator_apply,Set.mem_ofPred_eq,h,h',ite_false,mul_zero,zero_mul]
  simp_rw [he]
  rw [← Finset.sum_mul]
  rw [mul_comm (p b),← mul_assoc]
  rw [ENNReal.mul_inv_cancel (recordMass_ne_zero p hp f b) (recordMass_ne_top p f b)]
  simp

lemma expectation_congr_on_support (p : PMF α) (F G : α → ℝ)
    (h : ∀ a, a ∈ p.support → F a=G a) : expectation p F=expectation p G := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : p a=0
  · simp only [ha,ENNReal.toReal_zero,zero_mul]
  · rw [h a ha]

/-- An event determined by the record can be pulled out of its conditional
expectation, exactly as for a finite sigma-field. -/
lemma conditional_inter_expectation (p : PMF α) (hp : ∀ a, a ∈ p.support)
    (f : α → β) (E H : Set α)
    (hE : ∀ a b, f b=f a → (b ∈ E ↔ a ∈ E)) (a : α) :
    expectation (recordConditional p hp f a) ((E ∩ H).indicator fun _ => (1 : ℝ)) =
      if a ∈ E then expectation (recordConditional p hp f a) (H.indicator fun _ => (1 : ℝ))
      else 0 := by
  by_cases ha : a ∈ E
  · rw [ite_eq_left ha]
    apply expectation_congr_on_support
    intro b hb
    have hrec := (PMF.mem_support_filter_iff _).1 hb
    have hbE := (hE a b hrec.1).2 ha
    by_cases hbH : b ∈ H <;> simp [hbE,hbH]
  · rw [ite_eq_right ha,← expectation_const (recordConditional p hp f a) 0]
    apply expectation_congr_on_support
    intro b hb
    have hrec := (PMF.mem_support_filter_iff _).1 hb
    have hbE : b ∉ E := fun h => ha ((hE a b hrec.1).1 h)
    simp [hbE]

/-- One genuine exploration step: a conditional upper bound on every record
of a past event gives a multiplicative unconditional bound. -/
theorem record_step_le (p : PMF α) (hp : ∀ a, a ∈ p.support) (f : α → β)
    (E H : Set α) (hE : ∀ a b, f b=f a → (b ∈ E ↔ a ∈ E)) (c : ℝ)
    (hc : ∀ a ∈ E, expectation (recordConditional p hp f a)
      (H.indicator fun _ => (1 : ℝ)) ≤ c) :
    expectation p ((E ∩ H).indicator fun _ => (1 : ℝ)) ≤
      c * expectation p (E.indicator fun _ => (1 : ℝ)) := by
  conv_lhs => rw [← bind_recordConditional p hp f,expectation_bind]
  calc
    _ ≤ expectation p (E.indicator fun _ => c) := by
      apply expectation_mono
      intro a
      rw [conditional_inter_expectation p hp f E H hE a]
      by_cases ha : a ∈ E
      · simpa only [ha,ite_true,Set.indicator_of_mem ha] using hc a ha
      · simp only [ha,ite_false,Set.indicator_of_notMem ha,le_refl]
    _ = _ := by
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ E <;> simp [ha]; ring

end
end PottsDiscontinuity.TorusExploration
