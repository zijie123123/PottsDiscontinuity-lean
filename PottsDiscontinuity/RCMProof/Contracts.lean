module

public import Mathlib
public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.TorusLoops.LoopDensityLogBounds
public import PottsDiscontinuity.TorusRC.CorrelationRate
public import PottsDiscontinuity.TorusRC.OuterLowerLimit

/-!
# Source-level provider interfaces for the Theorem 1.2 assembly

This file records, as propositions, the lower-level statements consumed by the Theorem 1.2
assembly: Corollary 3.13(i)–(iii), equations (3.15), (3.16) and (3.19), and the corrected
Lemma 3.14. They are proved as `contract_cor313_i_proved`, `contract_cor313_ii_proved`,
`contract_cor313_iii_proved` (`RCMProof/Cor313Adapters.lean`), `contract_eq315_proved`
(`RCMProof/TorusRCAdapters.lean`), `TorusExploration.contract_eq316`
(`TorusExploration/Contract.lean`) and `corrected_lemma314_proved`
(`RCMProof/Lemma314Adapters.lean`). The crossing estimate `contract_h319` remains an explicit
hypothesis of the assembly; it is supplied by `TorusCrossing.h319_proved` in `Provider/`.
None of these propositions is a conclusion of the Theorem 1.2 assembly, and none is an axiom.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open Torus

noncomputable def torusLoopWeightFactor {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hNpos : 0 < N) (hMpos : 0 < M)
    (A : Torus.RCConfig N M) : ℝ :=
  Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ A : ℝ) *
    Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ))

noncomputable def torusWeightedRCMass {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hNpos : 0 < N) (hMpos : 0 < M)
    (A : Torus.RCConfig N M) : ℝ :=
  Torus.torusRCWeight hN hM q A * torusLoopWeightFactor hN hM q hNpos hMpos A

noncomputable def torusCorrespondenceScale (q : Set.Ici (1 : ℝ)) (N M : ℕ) : ℝ :=
  Real.rpow q.val ((N * M : ℝ) / 4) *
    Real.rpow (1 + Real.sqrt q.val) (-(N * M : ℝ))

noncomputable def criticalSixVertexParameter (q : Set.Ici (1 : ℝ)) : ℝ :=
  Real.sqrt (2 + Real.sqrt q.val)

/- Provider statement for Corollary 3.13(i) of the torus correspondence (`Torus/`), with the
project's fixed homological ell₀ and net indicator. Proved as `contract_cor313_i_proved`. -/
def contract_cor313_i : Prop :=
  ∀ (q : Set.Ici (1 : ℝ)) (_hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNpos : 0 < N) (hMpos : 0 < M),
      (∑ A : Torus.RCConfig N M, torusWeightedRCMass hN hM q hNpos hMpos A) =
        torusCorrespondenceScale q N M *
          SixVertex.Z6V (criticalSixVertexParameter q) N M

/- Provider statement for Corollary 3.13(ii) of the torus correspondence (`Torus/`).
Proved as `contract_cor313_ii_proved`. -/
def contract_cor313_ii : Prop :=
  ∀ (q : Set.Ici (1 : ℝ)) (_hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNpos : 0 < N) (hMpos : 0 < M),
      (∑ A ∈ Finset.univ.filter
        (fun A : Torus.RCConfig N M =>
          Torus.rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1),
        torusWeightedRCMass hN hM q hNpos hMpos A) ≤
        4 * torusCorrespondenceScale q N M *
          SixVertex.Z6Vr (criticalSixVertexParameter q) N M 1

/- Provider statement for Corollary 3.13(iii) of the torus correspondence (`Torus/`).
Proved as `contract_cor313_iii_proved`. -/
def contract_cor313_iii : Prop :=
  ∀ (q : Set.Ici (1 : ℝ)) (_hq : 4 < q.val) (r N M : ℕ)
    (_hr : 1 ≤ r) (hN : Even N) (hM : Even M)
    (hNpos : 0 < N) (hMpos : 0 < M),
      torusCorrespondenceScale q N M *
        SixVertex.Z6Vr (criticalSixVertexParameter q) N M r ≤
      ∑ A ∈ Finset.univ.filter
        (fun A : Torus.RCConfig N M =>
          r ≤ Torus.rcVerticalWinding hN hM ⟨0, hMpos⟩ A),
        torusWeightedRCMass hN hM q hNpos hMpos A

/- Provider statement for (3.15), copied from `TorusRC.Eq315.eq315`. Its
explicit input is equation (3.19), `h319`; its rate is the canonical unique
rotated-free-limit rate, and its width sequence is divisible by eight. -/
def contract_eq315 : Prop :=
  ∀ (q : Set.Ici (1 : ℝ)), TorusRC.h319 q →
      ((-TorusRC.inverseCorrelationLength q : ℝ) : EReal) ≤
        TorusRC.torusRCUOneIteratedLiminf q

/- The sole explicit input of the proved (3.15) provider, equation
(3.19) in `TorusRC/CrossingContracts.lean`. It is proved by `TorusCrossing.h319_proved`
(`TorusCrossing/Final.lean`); it is kept separate from the implication-shaped exact eq315
statement above. -/
def contract_h319 : Prop :=
  ∀ (q : Set.Ici (1 : ℝ)), TorusRC.h319 q

/- Provider statement for (3.16), proved as `TorusExploration.contract_eq316` in
`TorusExploration/Contract.lean`, with the same free-limit rate convention as (3.15). -/
def contract_eq316 : Prop :=
  ∀ (q : Set.Ici (1 : ℝ))
    (μ : MeasureTheory.Measure PottsDiscontinuity.FK.LatticeConfiguration)
    (_hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (_hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0)
        (PottsDiscontinuity.diagonalSite n))) / (n : ℝ))
      Filter.atTop (nhds ξinv))
    (r : ℕ) (_hr : 1 ≤ r),
      Filter.limsup
        (fun n : ℕ => Filter.limsup
          (fun m : ℕ => TorusRC.positiveEvenVerticalTailRateE q r n m) Filter.atTop)
        Filter.atTop ≤ (-((r - 1 : ℕ) : ℝ) * ξinv : ℝ)

/- Corrected provider statement for Lemma 3.14, copied from
`TorusLoops.Lemma314Corrected.lemma_3_14_corrected_limsup`. The input and
conclusion are kept in the provider's square-lattice free-box and limsup forms. -/
def corrected_lemma314 : Prop :=
  ∀ (q : Set.Ici (1 : ℝ)),
    Filter.Tendsto
      (fun n => (((Classical.choose (FK.freeBoxLimit_existsUnique
        (TorusLoops.rectangleFKParameters q)))
          (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ))
      Filter.atTop (nhds 0) →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : {k : ℕ // 2 ≤ k}, ∀ (N : ℕ)
      (hN : Even N) (hN₀ : N₀.val ≤ N),
      Filter.limsup
        (fun n => abs (TorusLoops.windingLoopDensityLogRate hN (by omega) q n))
        Filter.atTop ≤ ε

/- The vertical loop structure when `U = 1` (exactly two loops with nonzero vertical
winding, with opposite unit windings) is not restated here: it is proved as
`TorusTopology.verticalWindingLoops_card_le_two_of_U_eq_one` and
`TorusTopology.U_one_vertical_loop_structure` and used by `Torus/Corollary313.lean`. It is a
loop-structure input, not any of the rate or theorem conclusions of the Theorem 1.2 assembly. -/

/- Theorem 3.1's general zero-root branch from BetheAnsatz/ZeroRootTheorem.lean
(the Bethe ansatz), in the source's full transfer-matrix coordinates. The provider theorem
also requires the explicit anisotropy condition `2 < c`. -/

end PottsDiscontinuity.RCMProof
