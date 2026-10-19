module

public import PottsDiscontinuity.Torus.Corollary313
public import PottsDiscontinuity.TorusTopology.NonzeroWindingTurning
public import PottsDiscontinuity.TorusTopology.ZeroWindingTurning

/-!
# Final torus random-cluster / six-vertex identities

The homological turning classifications proved in `TorusTopology/ZeroWindingTurning.lean`
and `TorusTopology/NonzeroWindingTurning.lean` discharge the explicit intermediate
premises used by `OrientedLoopWeight` and `Corollary313`. This module exposes the
Lemma 3.10 weight identity and all three parts of Corollary 3.13 without those
intermediate premises.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

private theorem turnPremises_of_turning_classification
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (A : RCConfig N M) :
    ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A := by
  constructor
  · intro q hv hh
    exact PottsDiscontinuity.TorusTopology.loopRotationNumber_eq_pm_one_of_zero_winding
      hN hM i j A q hv hh
  · intro q hw
    exact PottsDiscontinuity.TorusTopology.loopRotationNumber_eq_zero_of_nonzero_winding
      hN hM i j A q hw

/-- Lemma 3.10's corrected random-cluster weight is the normalization times the
sum of the compatible oriented-loop weights. -/
theorem lemma_3_10_weight_identity_final
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (A : RCConfig N M) :
    torusCorrectedRCWeight hN hM i j q A =
      torusNormalization q N M *
        (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
          orientedLoopWeight (Real.arcosh (Real.sqrt q.val / 2)) x.val
            (rcSmoothing A) x.property) := by
  have ht := turnPremises_of_turning_classification hN hM i j A
  exact torusCorrectedRCWeight_eq_normalization_mul_orientedSum
    hN hM i j q hq A ht.1 ht.2

/-- Corollary 3.13(i): the corrected random-cluster partition sum equals the
six-vertex partition function at `c = sqrt (2 + sqrt q)`. -/
theorem corollary_313_i_final
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (i : Fin N) (j : Fin M) :
    (∑ A : RCConfig N M, torusCorrectedRCWeight hN hM i j q A) =
      torusNormalization q N M *
        Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M := by
  exact corollary_313_i hN hM q hq i j
    (fun A => turnPremises_of_turning_classification hN hM i j A)

/-- Corollary 3.13(ii): the `U = 1` corrected random-cluster sector is bounded
by four times the one-defect six-vertex sector. -/
theorem corollary_313_ii_final
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (i : Fin N) (j : Fin M) :
    (∑ A : {A : RCConfig N M // rcVerticalWinding hN hM j A = 1},
      torusCorrectedRCWeight hN hM i j q A.val) ≤
      4 * torusNormalization q N M *
        Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 := by
  exact corollary_313_ii hN hM q hq i j
    (fun A => turnPremises_of_turning_classification hN hM i j A)

/-- Corollary 3.13(iii): every `r`-defect six-vertex sector is bounded by the
corrected random-cluster sector with vertical winding at least `r`. -/
theorem corollary_313_iii_final
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (i : Fin N) (j : Fin M) (r : ℕ) :
    torusNormalization q N M *
        Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      ∑ A : {A : RCConfig N M // r ≤ rcVerticalWinding hN hM j A},
        torusCorrectedRCWeight hN hM i j q A.val := by
  exact corollary_313_iii hN hM q hq i j r
    (fun A => turnPremises_of_turning_classification hN hM i j A)

end PottsDiscontinuity.Torus
