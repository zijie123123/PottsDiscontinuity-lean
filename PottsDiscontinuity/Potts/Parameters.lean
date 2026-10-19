module

public import PottsDiscontinuity.FK.Parameters
public import PottsDiscontinuity.Frozen.Defs.PottsCriticalBeta
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter

/-!
# Edwards–Sokal parameters

The bond probability is `1 - exp (-β)`. This also verifies the corrected
parameter identity in consequence 1 of Theorem 3.19: the source prints `p_c = 1 - e^{β_c}`,
whereas the coupling `p = 1 - e^{-β}` gives `p_c = 1 - e^{-β_c}`, which holds for the explicit
values `β_c = log (1 + √q)` and `p_c = √q / (1 + √q)`.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

/-- The bond probability corresponding to inverse temperature `β`. -/
def bondProbability (β : ℝ) : ℝ := 1 - Real.exp (-β)

theorem bondProbability_pos {β : ℝ} (hβ : 0 < β) : 0 < bondProbability β := by
  exact sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hβ))

theorem bondProbability_lt_one (β : ℝ) : bondProbability β < 1 := by
  exact sub_lt_self 1 (Real.exp_pos (-β))

@[simp] theorem one_sub_bondProbability (β : ℝ) :
    1 - bondProbability β = Real.exp (-β) := by
  unfold bondProbability
  ring

/-- The independent FK parameter carrier at the actual Potts parameters. -/
def fkParameters (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) : FK.Parameters where
  val := q
  property := by exact_mod_cast (show 1 ≤ q by omega)
  edgeProbability := ⟨bondProbability β, bondProbability_pos hβ, bondProbability_lt_one β⟩

@[simp] theorem fkParameters_val (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) :
    (fkParameters q hq β hβ).val = q := rfl

@[simp] theorem fkParameters_edgeParameter (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) :
    FK.edgeParameter (fkParameters q hq β hβ) = 1 - Real.exp (-β) := rfl

/-- The explicit critical parameters satisfy the corrected identity `p_c = 1 - e^{-β_c}`
(the source prints `p_c = 1 - e^{β_c}` in consequence 1 of Theorem 3.19). -/
theorem bondProbability_pottsCriticalBeta (q : ℕ) (hq : 2 ≤ q) :
    bondProbability (pottsCriticalBeta q) =
      (rcCriticalParameter ⟨(q : ℝ), by
        change (1 : ℝ) ≤ q
        exact_mod_cast (show 1 ≤ q by omega)⟩ : ℝ) := by
  have hpos : 0 < 1 + Real.sqrt (q : ℝ) := by positivity
  simp only [bondProbability, pottsCriticalBeta, rcCriticalParameter,
    Real.exp_neg, Real.exp_log hpos]
  field_simp
  ring

end

end PottsDiscontinuity.Potts
