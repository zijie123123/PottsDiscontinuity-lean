module

public import PottsDiscontinuity.TorusRC.TiltProbability

/-! # Complementary duality invariance of the tilted torus law -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus PottsDiscontinuity.SixVertex

variable {N M : ℕ}

private theorem translatedDualConfig_apply_nxt (A : RCConfig N M)
    (v : Fin N × Fin M) :
    translatedDualConfig A (nxt v.1, v.2) = Bool.not (A v) := by
  rw [translatedDualConfig, shiftRCConfig_nxt]
  rfl

/-- Translation followed by complementation is a bijection of indexed torus
configurations. Its inverse uses the opposite horizontal shift. -/
def translatedDualConfigEquiv : RCConfig N M ≃ RCConfig N M where
  toFun := translatedDualConfig
  invFun A := fun v => Bool.not (A (nxt v.1, v.2))
  left_inv A := by
    funext v
    change Bool.not (translatedDualConfig A (nxt v.1, v.2)) = A v
    rw [translatedDualConfig_apply_nxt]
    simp
  right_inv A := by
    funext v
    have h := translatedDualConfig_apply_nxt
      (fun w => Bool.not (A (nxt w.1, w.2))) (prv v.1, v.2)
    simpa only [nxt, prv, Equiv.apply_symm_apply, Bool.not_not] using h

private theorem torusRCTiltEventWeight_translatedDual
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) :
    torusRCTiltEventWeight hN hM q E =
      torusRCTiltEventWeight hN hM q
        (translatedDualConfig ⁻¹' E) := by
  classical
  unfold torusRCTiltEventWeight
  calc
    (∑ A, E.indicator (torusRCTiltWeight hN hM q) A) =
        ∑ A, E.indicator (torusRCTiltWeight hN hM q)
          (translatedDualConfigEquiv A) := by
      exact (Equiv.sum_comp translatedDualConfigEquiv
        (fun A => E.indicator (torusRCTiltWeight hN hM q) A)).symm
    _ = ∑ A, (translatedDualConfig ⁻¹' E).indicator
          (torusRCTiltWeight hN hM q) A := by
      apply Finset.sum_congr rfl
      intro A _
      change (if translatedDualConfig A ∈ E then
          torusRCTiltWeight hN hM q (translatedDualConfig A) else 0) =
        (if translatedDualConfig A ∈ E then torusRCTiltWeight hN hM q A else 0)
      by_cases hA : translatedDualConfig A ∈ E
      · simp only [hA, ite_true]
        exact (torusRCTiltWeight_translatedDual hN hM q A).symm
      · simp only [hA, ite_false]

/-- The normalized self-dual tilt assigns the same probability to an event and
to its inverse image under translated complementary duality. -/
theorem torusRCTiltProbability_translatedDual (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    torusRCTiltProbability hN hM q E =
      torusRCTiltProbability hN hM q (translatedDualConfig ⁻¹' E) := by
  unfold torusRCTiltProbability
  rw [torusRCTiltEventWeight_translatedDual hN hM q E]

/-- Translated complementary duality transfers a standard-law event bound with
the exact `q^2` loss used for the source's torus duality step. -/
theorem torusRCProbability_translatedDual_lower (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q (translatedDualConfig ⁻¹' E) / q.val ^ 2 ≤
      torusRCProbability hN hM q E := by
  have hqpos : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  have hq2 : 0 < q.val ^ 2 := pow_pos hqpos _
  have hE := torusRCTiltProbability_comparison hN hM q E
  have hdual := torusRCTiltProbability_comparison hN hM q
    (translatedDualConfig ⁻¹' E)
  have hinv := torusRCTiltProbability_translatedDual hN hM q E
  calc
    torusRCProbability hN hM q (translatedDualConfig ⁻¹' E) / q.val ^ 2 ≤
        (q.val * torusRCTiltProbability hN hM q (translatedDualConfig ⁻¹' E)) /
          q.val ^ 2 :=
      div_le_div_of_nonneg_right hdual.2 hq2.le
    _ = torusRCTiltProbability hN hM q E / q.val := by
      rw [hinv]
      field_simp [hqpos.ne']
    _ ≤ torusRCProbability hN hM q E := hE.1

end PottsDiscontinuity.TorusRC
