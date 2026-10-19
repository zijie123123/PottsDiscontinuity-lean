module

public import PottsDiscontinuity.Torus.DualLoopTransport
public import PottsDiscontinuity.Torus.RCWeight

/-! # The self-dual torus weight used in the crossing argument -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

/-- The source's self-dual weight: the standard RC loop weight with the
`q^s` net correction removed. Its normalized law is the measure denoted
`\widetilde φ_T` in the proof of (3.15). -/
noncomputable def torusRCTiltWeight (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) : ℝ :=
  torusNormalization q N M * Real.sqrt q.val ^ rcLoopCount hN hM A

theorem torusRCTiltWeight_eq_standard_div_net (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCTiltWeight hN hM q A =
      torusRCWeight hN hM q A / q.val ^ rcNetIndicator hN hM A := by
  have hq : q.val = (Real.sqrt q.val) ^ 2 := by
    rw [Real.sq_sqrt]
    exact le_trans (by norm_num) q.property
  have hpow : q.val ^ rcNetIndicator hN hM A =
      Real.sqrt q.val ^ (2 * rcNetIndicator hN hM A) := by
    calc
      q.val ^ rcNetIndicator hN hM A =
          ((Real.sqrt q.val) ^ 2) ^ rcNetIndicator hN hM A :=
        congrArg (fun t : ℝ => t ^ rcNetIndicator hN hM A) hq
      _ = Real.sqrt q.val ^ (2 * rcNetIndicator hN hM A) := by rw [pow_mul]
  have hroot : 0 < Real.sqrt q.val :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one q.property)
  have hden : Real.sqrt q.val ^ (2 * rcNetIndicator hN hM A) ≠ 0 :=
    pow_ne_zero _ hroot.ne'
  rw [torusRCTiltWeight, torusRCWeight_eq_loopWeight hN hM q A, hpow]
  rw [pow_add]
  field_simp [hden]

/-- The tilted weight is invariant under the translated complementary duality. -/
theorem torusRCTiltWeight_translatedDual (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusRCTiltWeight hN hM q A =
      torusRCTiltWeight hN hM q (translatedDualConfig A) := by
  exact congrArg (fun k => torusNormalization q N M * Real.sqrt q.val ^ k)
    (rcLoopCount_translatedDual hN hM A)

end PottsDiscontinuity.TorusRC
