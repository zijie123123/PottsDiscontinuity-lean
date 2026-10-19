module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Infra.Lambda
public import PottsDiscontinuity.RCMProof.RouteB
public import PottsDiscontinuity.RCMProof.Lemma314Adapters
public import PottsDiscontinuity.SixVertex.Sec33Dominance
public import PottsDiscontinuity.SixVertex.Sec33RealAnalysis

@[expose] public section

open Finset Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open SixVertex Torus

noncomputable def upperLoopFactor {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) : ℝ :=
  Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A : ℝ) *
    Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ))

private theorem upperLoopFactor_eq_densityWeight {N M : ℕ}
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    upperLoopFactor hN hM q hNp hMp A =
      TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A := by
  unfold upperLoopFactor TorusLoops.windingLoopDensityWeight TorusLoops.windingLoopDensityBase
  let k := TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A
  let s := Torus.rcNetIndicator hN hM A
  have hneg : Real.rpow q.val (-(s : ℝ)) = (q.val ^ s)⁻¹ := by
    calc
      Real.rpow q.val (-(s : ℝ)) = (Real.rpow q.val (s : ℝ))⁻¹ :=
        Real.rpow_neg (le_trans (by norm_num) q.property) (s : ℝ)
      _ = (q.val ^ s)⁻¹ := congrArg Inv.inv (Real.rpow_natCast q.val s)
  change Real.rpow (2 / Real.sqrt q.val) (k : ℝ) *
    Real.rpow q.val (-(s : ℝ)) = (2 / Real.sqrt q.val) ^ k / q.val ^ s
  calc
    Real.rpow (2 / Real.sqrt q.val) (k : ℝ) * Real.rpow q.val (-(s : ℝ)) =
        (2 / Real.sqrt q.val) ^ k * Real.rpow q.val (-(s : ℝ)) := by
      exact congrArg (fun x : ℝ => x * Real.rpow q.val (-(s : ℝ)))
        (Real.rpow_natCast (2 / Real.sqrt q.val) k)
    _ = (2 / Real.sqrt q.val) ^ k * (q.val ^ s)⁻¹ :=
      congrArg (fun x : ℝ => (2 / Real.sqrt q.val) ^ k * x) hneg
    _ = (2 / Real.sqrt q.val) ^ k / q.val ^ s :=
      (div_eq_mul_inv _ _).symm

private theorem upperLoopFactor_le_one {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) : upperLoopFactor hN hM q hNp hMp A ≤ 1 := by
  have hsqrt : 2 < Real.sqrt q.val := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ q.val)
    nlinarith [Real.sqrt_nonneg q.val]
  have hbase : TorusLoops.windingLoopDensityUpperBase q = 1 := by
    unfold TorusLoops.windingLoopDensityUpperBase TorusLoops.windingLoopDensityBase
    rw [max_eq_left]
    rw [div_le_one (by positivity)]
    linarith
  rw [upperLoopFactor_eq_densityWeight hN hM q hNp hMp A]
  calc
    TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A ≤
        TorusLoops.windingLoopDensityUpperBase q ^ (N + M) :=
      TorusLoops.windingLoopDensityWeight_le_global hN hM hNp hMp q A
    _ = 1 := by rw [hbase]; simp

noncomputable def upperTailRateE
    (q : Set.Ici (1 : ℝ)) (r n m : ℕ) : EReal :=
  TorusRC.positiveEvenVerticalTailRateE q r n m

private theorem upperTailRateE_nonpos
    (q : Set.Ici (1 : ℝ)) (r n m : ℕ) : upperTailRateE q r n m ≤ 0 := by
  apply EReal.coe_le_coe_iff.mpr
  dsimp [upperTailRateE, TorusRC.positiveEvenVerticalTailRateE,
    TorusRC.positiveEvenVerticalTailRate]
  exact div_nonpos_of_nonpos_of_nonneg
    (TorusRC.torusRCVerticalTail_log_nonpos _ _ q _ r) (Nat.cast_nonneg _)

private theorem upperTailRateE_inner_limsup_nonpos
    (q : Set.Ici (1 : ℝ)) (r n : ℕ) :
    Filter.limsup (fun m => upperTailRateE q r n m) atTop ≤ 0 := by
  have h := Filter.limsup_le_limsup
    (f := atTop) (u := fun m => upperTailRateE q r n m)
    (v := fun _ : ℕ => (0 : EReal)) (Filter.Eventually.of_forall (upperTailRateE_nonpos q r n))
  simpa using h

private theorem upperTailRateEventually
    (hW21 : contract_eq316) (q : Set.Ici (1 : ℝ))
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv))
    (hξ : 0 < ξinv) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q 2 n m < -3 * ξinv / 4 := by
  let u : ℕ → EReal := fun n => Filter.limsup
    (fun m => upperTailRateE q 2 n m) atTop
  have huPoint (n : ℕ) : u n ≤ 0 := upperTailRateE_inner_limsup_nonpos q 2 n
  have huBounded : Filter.IsBoundedUnder (· ≤ ·) atTop u := by
    apply Filter.isBoundedUnder_of_eventually_le
    exact Filter.Eventually.of_forall huPoint
  have houter := hW21 q μ hμ ξinv hRate 2 (by norm_num)
  have houter' : Filter.limsup u atTop ≤ (-ξinv : EReal) := by
    simpa [u, upperTailRateE] using houter
  have htarget : (-ξinv : ℝ) < -3 * ξinv / 4 := by nlinarith
  have houterStrict : Filter.limsup u atTop < ((-3 * ξinv / 4 : ℝ) : EReal) := by
    exact lt_of_le_of_lt houter' (EReal.coe_lt_coe_iff.mpr htarget)
  have hn : ∀ᶠ n : ℕ in atTop, u n < ((-3 * ξinv / 4 : ℝ) : EReal) :=
    Filter.eventually_lt_of_limsup_lt houterStrict huBounded
  filter_upwards [hn] with n hn
  have hmBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun m => upperTailRateE q 2 n m) := by
    apply Filter.isBoundedUnder_of_eventually_le
    exact Filter.Eventually.of_forall (upperTailRateE_nonpos q 2 n)
  have hm := Filter.eventually_lt_of_limsup_lt hn hmBounded
  filter_upwards [hm] with m hm
  exact EReal.coe_lt_coe_iff.mp hm

private theorem upperTailRateEventually_general
    (hW21 : contract_eq316) (q : Set.Ici (1 : ℝ))
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv))
    {r : ℕ} (hr1 : 1 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q r n m <
        -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
  let u : ℕ → EReal := fun n => Filter.limsup
    (fun m => upperTailRateE q r n m) atTop
  have huPoint (n : ℕ) : u n ≤ 0 := upperTailRateE_inner_limsup_nonpos q r n
  have huBounded : Filter.IsBoundedUnder (· ≤ ·) atTop u := by
    apply Filter.isBoundedUnder_of_eventually_le
    exact Filter.Eventually.of_forall huPoint
  have houter := hW21 q μ hμ ξinv hRate r hr1
  have hbase : -((r - 1 : ℕ) : ℝ) * ξinv <
      -((r - 1 : ℕ) : ℝ) * ξinv + δ := by linarith
  have houter' : Filter.limsup u atTop ≤
      ((-((r - 1 : ℕ) : ℝ) * ξinv : ℝ) : EReal) := by
    simpa [u, upperTailRateE] using houter
  have houterStrict : Filter.limsup u atTop <
      ((-((r - 1 : ℕ) : ℝ) * ξinv + δ : ℝ) : EReal) :=
    lt_of_le_of_lt houter' (EReal.coe_lt_coe_iff.mpr hbase)
  have hn : ∀ᶠ n : ℕ in atTop, u n <
      ((-((r - 1 : ℕ) : ℝ) * ξinv + δ : ℝ) : EReal) :=
    Filter.eventually_lt_of_limsup_lt houterStrict huBounded
  filter_upwards [hn] with n hn
  have hmBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun m => upperTailRateE q r n m) := by
    apply Filter.isBoundedUnder_of_eventually_le
    exact Filter.Eventually.of_forall (upperTailRateE_nonpos q r n)
  have hm := Filter.eventually_lt_of_limsup_lt hn hmBounded
  filter_upwards [hm] with m hm
  exact EReal.coe_lt_coe_iff.mp hm

noncomputable def upperTailProbability
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hMp : 0 < M) (r : ℕ) : ℝ :=
  TorusRC.torusRCProbability hN hM q
    (TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r)

noncomputable def upperLoopExpectation
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNp : 0 < N) (hMp : 0 < M) : ℝ :=
  ∑ A : RCConfig N M, TorusRC.torusRCMass hN hM q A *
    upperLoopFactor hN hM q hNp hMp A

private theorem upperLoopExpectation_eq_densityExpectation
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNp : 0 < N) (hMp : 0 < M) :
    upperLoopExpectation hN hM q hNp hMp =
      TorusLoops.phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
  unfold upperLoopExpectation TorusLoops.phi_T_windingLoopDensityExpectation
  apply Finset.sum_congr rfl
  intro A hA
  rw [upperLoopFactor_eq_densityWeight hN hM q hNp hMp A]

private theorem upperLoopExpectation_rate_eq
    {N : ℕ} (hN : Even N) (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (m : ℕ) :
    TorusLoops.windingLoopDensityLogRate hN hNp q m =
      Real.log (upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m)
        q hNp (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ) := by
  simp [TorusLoops.windingLoopDensityLogRate, TorusRC.positiveEvenPeriod,
    upperLoopExpectation_eq_densityExpectation]

private theorem upperLoopExpectation_abs_log_rate_eventually
    {N : ℕ} (hN : Even N) (q : Set.Ici (1 : ℝ)) (hNp : 0 < N)
    (lim : ℝ)
    (hlim : Filter.limsup
      (fun m => abs (TorusLoops.windingLoopDensityLogRate hN hNp q m)) atTop ≤ lim)
    (hbounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun m => abs (TorusLoops.windingLoopDensityLogRate hN hNp q m)))
    {bound : ℝ} (hbound : lim < bound) :
    ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m)
        q hNp (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ bound := by
  have hevent := Filter.eventually_lt_of_limsup_lt
    (lt_of_le_of_lt hlim hbound) hbounded
  filter_upwards [hevent] with m hm
  simpa [upperLoopExpectation_rate_eq] using hm.le

private theorem upperTailFactorization
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) (hr1 : 1 ≤ r) :
    SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
        (upperTailProbability hN hM q hMp r / upperLoopExpectation hN hM q hNp hMp) := by
  classical
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let E : Set (RCConfig N M) :=
    TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r
  let Er : Set (RCConfig N M) :=
    {A | r ≤ Torus.rcVerticalWinding hN hM ⟨0, hMp⟩ A}
  let f : RCConfig N M → ℝ := upperLoopFactor hN hM q hNp hMp
  let w : RCConfig N M → ℝ := Torus.torusRCWeight hN hM q
  let C : ℝ := Torus.torusNormalization q N M
  have hscale : 0 < C := by dsimp [C]; exact Torus.torusNormalization_pos q N M
  have hZ : 0 < SixVertex.Z6V c N M := by
    apply SixVertex.Z6V_pos
    · dsimp [c]; positivity
    · exact hNp
    · exact hMp
  have hZr : 0 < SixVertex.Z6Vr c N M r := by
    apply SixVertex.Z6Vr_pos
    · dsimp [c]; positivity
    · exact hNp
    · exact hMp
    · exact hr
  have htotalContract := hW12i q hq N M hN hM hNp hMp
  change (∑ A : RCConfig N M, w A * f A) =
    C * SixVertex.Z6V c N M at htotalContract
  have hsectorContract := hW12iii q hq r N M hr1 hN hM hNp hMp
  change C * SixVertex.Z6Vr c N M r ≤
    ∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ Er), w A * f A
    at hsectorContract
  have hsub : Finset.univ.filter (fun A : RCConfig N M => A ∈ Er) ⊆
      Finset.univ.filter (fun A : RCConfig N M => A ∈ E) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact hA
  have hpartitionPos : 0 < TorusRC.torusRCPartition hN hM q :=
    TorusRC.torusRCPartition_pos hN hM q
  have hprobEq : TorusRC.torusRCProbability hN hM q E =
      (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) /
        TorusRC.torusRCPartition hN hM q := by
    rw [TorusRC.torusRCProbability_eq_sum]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp_rw [TorusRC.torusRCMass, w]
    rw [← Finset.sum_div]
  have htailMass :
      (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ Er), w A * f A) ≤
        TorusRC.torusRCPartition hN hM q *
          TorusRC.torusRCProbability hN hM q E := by
    calc
      _ ≤ ∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A * f A := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro A hA hnot
        have hw : 0 ≤ w A := (TorusRC.torusRCWeight_pos hN hM q A).le
        have hf : 0 ≤ f A := by
          dsimp [f, upperLoopFactor]
          positivity
        exact mul_nonneg hw hf
      _ ≤ ∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A := by
        apply Finset.sum_le_sum
        intro A hA
        have hw : 0 ≤ w A := (TorusRC.torusRCWeight_pos hN hM q A).le
        have hf := upperLoopFactor_le_one hN hM q hq hNp hMp A
        dsimp [w, f]
        exact mul_le_of_le_one_right hw hf
      _ = TorusRC.torusRCPartition hN hM q *
          TorusRC.torusRCProbability hN hM q E := by
        rw [hprobEq]
        field_simp
  have hsectorTail : C * SixVertex.Z6Vr c N M r ≤
      TorusRC.torusRCPartition hN hM q *
        TorusRC.torusRCProbability hN hM q E := hsectorContract.trans htailMass
  have hsumNormalized : upperLoopExpectation hN hM q hNp hMp =
      (∑ A : RCConfig N M, w A * f A) / TorusRC.torusRCPartition hN hM q := by
    unfold upperLoopExpectation
    calc
      (∑ A : RCConfig N M, TorusRC.torusRCMass hN hM q A *
          upperLoopFactor hN hM q hNp hMp A) =
        ∑ A : RCConfig N M, (w A * f A) /
          TorusRC.torusRCPartition hN hM q := by
        apply Finset.sum_congr rfl
        intro A hA
        simp only [TorusRC.torusRCMass, w, f]
        field_simp [ne_of_gt hpartitionPos]
      _ = (∑ A : RCConfig N M, w A * f A) /
          TorusRC.torusRCPartition hN hM q := by rw [Finset.sum_div]
  have htotalNormalized : upperLoopExpectation hN hM q hNp hMp *
      TorusRC.torusRCPartition hN hM q = C * SixVertex.Z6V c N M := by
    rw [hsumNormalized, htotalContract]
    field_simp [ne_of_gt hpartitionPos]
  have htotalPos : 0 < upperLoopExpectation hN hM q hNp hMp := by
    have hp := TorusRC.torusRCPartition_pos hN hM q
    have hz' : 0 < C * SixVertex.Z6V c N M := mul_pos hscale hZ
    nlinarith [htotalNormalized]
  have hratio : SixVertex.Z6Vr c N M r ≤
      SixVertex.Z6V c N M *
        (TorusRC.torusRCProbability hN hM q E / upperLoopExpectation hN hM q hNp hMp) := by
    have hP : TorusRC.torusRCPartition hN hM q =
        C * SixVertex.Z6V c N M / upperLoopExpectation hN hM q hNp hMp := by
      calc
        TorusRC.torusRCPartition hN hM q =
            (upperLoopExpectation hN hM q hNp hMp *
              TorusRC.torusRCPartition hN hM q) /
                upperLoopExpectation hN hM q hNp hMp := by
          field_simp [ne_of_gt htotalPos]
        _ = C * SixVertex.Z6V c N M /
            upperLoopExpectation hN hM q hNp hMp := by rw [htotalNormalized]
    have hmul : C * SixVertex.Z6Vr c N M r ≤
        C * (SixVertex.Z6V c N M *
          (TorusRC.torusRCProbability hN hM q E /
            upperLoopExpectation hN hM q hNp hMp)) := by
      calc
        C * SixVertex.Z6Vr c N M r ≤
            (C * SixVertex.Z6V c N M /
              upperLoopExpectation hN hM q hNp hMp) *
                TorusRC.torusRCProbability hN hM q E := by
          simpa [hP] using hsectorTail
        _ = C * (SixVertex.Z6V c N M *
            (TorusRC.torusRCProbability hN hM q E /
              upperLoopExpectation hN hM q hNp hMp)) := by
          field_simp [ne_of_gt htotalPos]
    exact (mul_le_mul_iff_of_pos_left hscale).mp hmul
  simpa [c, E, upperTailProbability, upperLoopExpectation] using hratio

private theorem upperLoopExpectation_pos
    (hW12i : contract_cor313_i) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (N M : ℕ) (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) :
    0 < upperLoopExpectation hN hM q hNp hMp := by
  let f : RCConfig N M → ℝ := upperLoopFactor hN hM q hNp hMp
  let w : RCConfig N M → ℝ := Torus.torusRCWeight hN hM q
  let C : ℝ := Torus.torusNormalization q N M
  have hC : 0 < C := by dsimp [C]; exact Torus.torusNormalization_pos q N M
  have hZ : 0 < SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M := by
    exact SixVertex.Z6V_pos (by positivity) hNp hMp
  have hP : 0 < TorusRC.torusRCPartition hN hM q :=
    TorusRC.torusRCPartition_pos hN hM q
  have hcontract := hW12i q hq N M hN hM hNp hMp
  change (∑ A : RCConfig N M, w A * f A) =
    C * SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M at hcontract
  have hsum : upperLoopExpectation hN hM q hNp hMp =
      (∑ A : RCConfig N M, w A * f A) / TorusRC.torusRCPartition hN hM q := by
    unfold upperLoopExpectation
    calc
      (∑ A : RCConfig N M, TorusRC.torusRCMass hN hM q A *
          upperLoopFactor hN hM q hNp hMp A) =
        ∑ A : RCConfig N M, (w A * f A) /
          TorusRC.torusRCPartition hN hM q := by
        apply Finset.sum_congr rfl
        intro A hA
        simp only [TorusRC.torusRCMass, w, f]
        field_simp [ne_of_gt hP]
      _ = (∑ A : RCConfig N M, w A * f A) /
          TorusRC.torusRCPartition hN hM q := by rw [Finset.sum_div]
  rw [hsum, hcontract]
  exact div_pos (mul_pos hC hZ) hP

private theorem upperTailProbability_pos
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) (hr1 : 1 ≤ r) :
    0 < upperTailProbability hN hM q hMp r := by
  have hE := upperLoopExpectation_pos hW12i q hq N M hN hM hNp hMp
  have hZ : 0 < SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M := by
    exact SixVertex.Z6V_pos (by positivity) hNp hMp
  have hZr : 0 < SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r := by
    exact SixVertex.Z6Vr_pos (by positivity) hNp hMp hr
  have hfactor := upperTailFactorization hW12i hW12iii q hq N M hN hM hNp hMp
    (r := r) hr hr1
  have hpnonneg : 0 ≤ upperTailProbability hN hM q hMp r :=
    TorusRC.torusRCProbability_nonneg hN hM q _
  by_contra hnot
  have hpnonpos : upperTailProbability hN hM q hMp r ≤ 0 := le_of_not_gt hnot
  have hratioNonpos : upperTailProbability hN hM q hMp r /
      upperLoopExpectation hN hM q hNp hMp ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hpnonpos hE.le
  have hprodNonpos : SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
      (upperTailProbability hN hM q hMp r /
        upperLoopExpectation hN hM q hNp hMp) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hZ.le hratioNonpos
  linarith [hfactor]

private theorem pow_positiveEvenPeriod (x : ℝ) (m : ℕ) :
    x ^ TorusRC.positiveEvenPeriod m = x ^ 2 * (x ^ 2) ^ m := by
  rw [show TorusRC.positiveEvenPeriod m = 2 + 2 * m by
    simp [TorusRC.positiveEvenPeriod]; omega]
  rw [pow_add, ← pow_mul]

private theorem upperDominanceGap_fixedIndex
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (ξinv : ℝ) (hξ : 0 < ξinv) (n Nloop : ℕ)
    (hNloop : Nloop ≤ TorusRC.positiveEvenPeriod n)
    (hTail : ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q 2 n m < -3 * ξinv / 4)
    (hLoop : ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
        (TorusRC.positiveEvenPeriod_even m) q
        (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ ξinv / 32)
    {r : ℕ} (hr : r ≤ TorusRC.positiveEvenPeriod n / 2) (hr2 : 2 ≤ r) :
    Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
      (TorusRC.positiveEvenPeriod n) r) ≤
      Real.log (SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val))
        (TorusRC.positiveEvenPeriod n)) - ξinv / 2 := by
  classical
  let N := TorusRC.positiveEvenPeriod n
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let Lr : ℝ := SixVertex.Lambda c N r
  let Lmax : ℝ := SixVertex.LambdaMax c N
  let D : ℝ := Lmax ^ 2
  let K : ℝ := (2 ^ N : ℝ) * D
  let X : ℕ → ℝ := fun m => Lr ^ TorusRC.positiveEvenPeriod m
  let Y : ℕ → ℝ := fun m =>
    upperTailProbability (TorusRC.positiveEvenPeriod_even n)
      (TorusRC.positiveEvenPeriod_even m) q
      (TorusRC.positiveEvenPeriod_pos m) 2 /
    upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
      (TorusRC.positiveEvenPeriod_even m) q
      (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)
  let Z : ℕ → ℝ := fun m =>
    (2 ^ N : ℝ) * Lmax ^ TorusRC.positiveEvenPeriod m
  have hN : Even N := by dsimp [N]; exact TorusRC.positiveEvenPeriod_even n
  have hNp : 0 < N := by dsimp [N]; exact TorusRC.positiveEvenPeriod_pos n
  have hNhalf : 2 ≤ N / 2 := by omega
  have hc : 0 < c := by dsimp [c]; positivity
  have hLr : 0 < Lr := by
    dsimp [Lr, N, c]
    exact SixVertex.Lambda_pos (by positivity) hr
  have hLmax : 0 < Lmax := by
    dsimp [Lmax, N, c]
    exact SixVertex.LambdaMax_pos (by positivity)
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hEpos (m : ℕ) : 0 < upperLoopExpectation
      (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_even m) q
      (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m) :=
    upperLoopExpectation_pos hW12i q hq N (TorusRC.positiveEvenPeriod m) hN
      (TorusRC.positiveEvenPeriod_even m) hNp (TorusRC.positiveEvenPeriod_pos m)
  have hYpos : ∀ᶠ m : ℕ in atTop, 0 < Y m := by
    filter_upwards with m
    have htailpos := upperTailProbability_pos hW12i hW12iii q hq N
      (TorusRC.positiveEvenPeriod m) hN (TorusRC.positiveEvenPeriod_even m)
      hNp (TorusRC.positiveEvenPeriod_pos m) (r := 2) (by omega) (by norm_num)
    exact div_pos htailpos (hEpos m)
  have hZpos : ∀ᶠ m : ℕ in atTop, 0 < Z m := by
    filter_upwards with m
    dsimp [Z]
    positivity
  have hlower : ∀ᶠ m : ℕ in atTop, (Lr ^ 2) * (Lr ^ 2) ^ m ≤ X m := by
    filter_upwards with m
    change (Lr ^ 2) * (Lr ^ 2) ^ m ≤ Lr ^ TorusRC.positiveEvenPeriod m
    rw [pow_positiveEvenPeriod]
  have hupper : ∀ᶠ m : ℕ in atTop, X m ≤ Y m * Z m := by
    filter_upwards with m
    let M := TorusRC.positiveEvenPeriod m
    have hM : Even M := by dsimp [M]; exact TorusRC.positiveEvenPeriod_even m
    have hMp : 0 < M := by dsimp [M]; exact TorusRC.positiveEvenPeriod_pos m
    have htrace := SixVertex.Lambda_pow_le_Z6Vr_even hc hNp hMp hr hM
    have hsector := upperTailFactorization hW12i hW12iii q hq N M hN hM hNp hMp
      (r := r) hr (by omega)
    have htailMono : upperTailProbability hN hM q hMp r ≤
        upperTailProbability hN hM q hMp 2 := by
      apply TorusRC.torusRCProbability_mono hN hM q
      intro A hA
      change r ≤ Torus.rcVerticalWinding hN hM ⟨0, hMp⟩ A at hA
      change 2 ≤ Torus.rcVerticalWinding hN hM ⟨0, hMp⟩ A
      exact le_trans (by omega) hA
    have htailRatioMono : upperTailProbability hN hM q hMp r /
        upperLoopExpectation hN hM q hNp hMp ≤
      upperTailProbability hN hM q hMp 2 /
        upperLoopExpectation hN hM q hNp hMp :=
      div_le_div_of_nonneg_right htailMono (hEpos m).le
    have hwhole := SixVertex.Z6V_le_two_pow_mul_LambdaMax_pow hc hNp hMp
    have htail2pos := upperTailProbability_pos hW12i hW12iii q hq N M hN hM hNp hMp
      (r := 2) (by omega) (by norm_num)
    have hratio2pos : 0 < upperTailProbability hN hM q hMp 2 /
        upperLoopExpectation hN hM q hNp hMp := div_pos htail2pos (hEpos m)
    calc
      X m ≤ SixVertex.Z6Vr
          (Real.sqrt (2 + Real.sqrt q.val)) N M r := by
        simpa [X, Lr, c, N, M] using htrace
      _ ≤ SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N
          M * (upperTailProbability hN hM q hMp r /
            upperLoopExpectation hN hM q hNp hMp) := by
        simpa [N, M] using hsector
      _ ≤ SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
          (upperTailProbability hN hM q hMp 2 /
            upperLoopExpectation hN hM q hNp hMp) :=
        mul_le_mul_of_nonneg_left htailRatioMono
          (SixVertex.Z6V_pos hc hNp hMp).le
      _ ≤ ((2 ^ N : ℝ) * SixVertex.LambdaMax
            (Real.sqrt (2 + Real.sqrt q.val)) N ^ M) *
          (upperTailProbability hN hM q hMp 2 /
            upperLoopExpectation hN hM q hNp hMp) :=
        mul_le_mul_of_nonneg_right hwhole hratio2pos.le
      _ = Y m * Z m := by
        dsimp [Y, Z, Lmax, N, M]
        ring
  have hYrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (1 / (m : ℝ)) * Real.log (Y m) ≤ -ξinv + ε := by
    intro ε hε
    rcases Filter.eventually_atTop.1 hTail with ⟨m₀, hm₀⟩
    filter_upwards [Filter.eventually_ge_atTop (max m₀ 1), hLoop] with m hm hmLoop
    have hm0 : m₀ ≤ m := le_trans (Nat.le_max_left _ _) hm
    have hmpos : 0 < m := lt_of_lt_of_le (by omega) (le_trans (Nat.le_max_right _ _) hm)
    have htail := hm₀ m hm0
    let M := TorusRC.positiveEvenPeriod m
    let p := upperTailProbability hN (TorusRC.positiveEvenPeriod_even m) q
      (TorusRC.positiveEvenPeriod_pos m) 2
    let e := upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m) q hNp
      (TorusRC.positiveEvenPeriod_pos m)
    have hp : 0 < p := by
      dsimp [p]
      exact upperTailProbability_pos hW12i hW12iii q hq N M hN
        (TorusRC.positiveEvenPeriod_even m) hNp (TorusRC.positiveEvenPeriod_pos m)
        (r := 2) (by omega) (by norm_num)
    have he : 0 < e := by dsimp [e]; exact hEpos m
    have htailRate : Real.log p / (M : ℝ) < -3 * ξinv / 4 := by
      simpa [p, M, upperTailProbability, TorusRC.positiveEvenVerticalTailRate,
        TorusRC.positiveEvenPeriod_even] using htail
    have hMcast : (M : ℝ) = 2 * ((m : ℝ) + 1) := by
      dsimp [M, TorusRC.positiveEvenPeriod]
      push_cast
      ring
    have hmcast : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hmone : 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hmpos.ne')
    have hratioLo : 2 ≤ (M : ℝ) / (m : ℝ) := by
      rw [hMcast]
      field_simp
      nlinarith [hmone]
    have hratioHi : (M : ℝ) / (m : ℝ) ≤ 4 := by
      rw [hMcast]
      field_simp
      nlinarith
    have htailNeg : Real.log p / (M : ℝ) < 0 := by
      linarith [hξ]
    have htailScaled : ((M : ℝ) / (m : ℝ)) * (Real.log p / (M : ℝ)) <
        -3 * ξinv / 2 := by
      calc
        _ ≤ 2 * (Real.log p / (M : ℝ)) :=
          mul_le_mul_of_nonpos_right hratioLo htailNeg.le
        _ < -3 * ξinv / 2 := by nlinarith [htailRate]
    have hMpos : 0 < M := by dsimp [M]; exact TorusRC.positiveEvenPeriod_pos m
    have hloopBound' : |Real.log e / (M : ℝ)| ≤ ξinv / 32 := by
      simpa [e, M] using hmLoop
    have hloopUpper : -Real.log e / (M : ℝ) ≤ ξinv / 32 := by
      have := (abs_le.mp hloopBound').1
      simpa [neg_div] using neg_le_neg this
    have hloopScaled : ((M : ℝ) / (m : ℝ)) * (-Real.log e / (M : ℝ)) ≤
        ξinv / 8 := by
      calc
        _ ≤ ((M : ℝ) / (m : ℝ)) * (ξinv / 32) :=
          mul_le_mul_of_nonneg_left hloopUpper (by positivity)
        _ ≤ 4 * (ξinv / 32) :=
          mul_le_mul_of_nonneg_right hratioHi (by positivity)
        _ = ξinv / 8 := by ring
    have hYlog : Real.log (Y m) = Real.log p - Real.log e := by
      dsimp [Y, p, e]
      rw [Real.log_div hp.ne' he.ne']
    have hscaledEq : (1 / (m : ℝ)) * Real.log (Y m) =
        ((M : ℝ) / (m : ℝ)) * (Real.log p / (M : ℝ) - Real.log e / (M : ℝ)) := by
      rw [hYlog]
      have hMcastNe : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
      field_simp [hmcast.ne', hMcastNe]
    rw [hscaledEq]
    exact (calc
      ((M : ℝ) / (m : ℝ)) *
          (Real.log p / (M : ℝ) - Real.log e / (M : ℝ)) =
        ((M : ℝ) / (m : ℝ)) * (Real.log p / (M : ℝ)) +
          ((M : ℝ) / (m : ℝ)) * (-Real.log e / (M : ℝ)) := by ring
      _ < -3 * ξinv / 2 + ξinv / 8 := add_lt_add_of_lt_of_le htailScaled hloopScaled
      _ < -ξinv + ε := by nlinarith [hξ, hε]).le
  have hZfactor (m : ℕ) : Z m = K * D ^ m := by
    dsimp [Z, K, D]
    calc
      (2 ^ N : ℝ) * Lmax ^ TorusRC.positiveEvenPeriod m =
          (2 ^ N : ℝ) * (Lmax ^ 2 * (Lmax ^ 2) ^ m) := by
        exact congrArg (fun z : ℝ => (2 ^ N : ℝ) * z) (pow_positiveEvenPeriod Lmax m)
      _ = ((2 ^ N : ℝ) * Lmax ^ 2) * (Lmax ^ 2) ^ m := by ring
  have hZrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (1 / (m : ℝ)) * Real.log (Z m) ≤ Real.log D + ε := by
    intro ε hε
    have hconst : Tendsto (fun m : ℕ => (1 / (m : ℝ)) * Real.log K)
        atTop (𝓝 0) := by
      have h := tendsto_one_div_atTop_nhds_zero_nat.mul_const (Real.log K)
      simpa using h
    have hconv : Tendsto (fun m : ℕ => Real.log D +
        (1 / (m : ℝ)) * Real.log K) atTop (𝓝 (Real.log D)) := by
      simpa using (tendsto_const_nhds.add hconst)
    have hEq : (fun m : ℕ => (1 / (m : ℝ)) * Real.log (Z m)) =ᶠ[atTop]
        (fun m : ℕ => Real.log D + (1 / (m : ℝ)) * Real.log K) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with m hm
      have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hpow : D ^ m ≠ 0 := pow_ne_zero _ hD.ne'
      rw [hZfactor m, Real.log_mul hK.ne' hpow, Real.log_pow]
      field_simp
      ring
    have hconv' := hconv.congr' hEq.symm
    filter_upwards [hconv'.eventually (Iio_mem_nhds (by linarith :
      Real.log D < Real.log D + ε))] with m hm
    exact hm.le
  have hgrowth := SixVertex.log_growth_le_of_eventually_factorized
    (C := Lr ^ 2) (Λ := Lr ^ 2) (Λmax := D) (a := -ξinv) (b := 0)
    (by positivity) (by positivity) X Y Z hYpos hZpos hlower hupper hYrate
    (by simpa using hZrate)
  have hlogpow := hgrowth
  rw [Real.log_pow, Real.log_pow] at hlogpow
  dsimp [Lr, Lmax, c, N] at hlogpow ⊢
  nlinarith

private theorem sectorLogRate_le_of_eventual_tail
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (n : ℕ)
    (ξinv δ : ℝ) {r : ℕ} (hr : r ≤
      TorusRC.positiveEvenPeriod n / 2) (hr1 : 1 ≤ r)
    (hcenter : SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val))
      (TorusRC.positiveEvenPeriod n) =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          (TorusRC.positiveEvenPeriod n) 0)
    (hTail : ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q r n m <
        -((r - 1 : ℕ) : ℝ) * ξinv + δ / 2)
    (hLoop : ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
        (TorusRC.positiveEvenPeriod_even m) q (TorusRC.positiveEvenPeriod_pos n)
        (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ δ / 2) :
    Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
      (TorusRC.positiveEvenPeriod n) r /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          (TorusRC.positiveEvenPeriod n) 0) ≤
      -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
  classical
  let N := TorusRC.positiveEvenPeriod n
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let p (m : ℕ) := upperTailProbability (TorusRC.positiveEvenPeriod_even n)
    (TorusRC.positiveEvenPeriod_even m) q (TorusRC.positiveEvenPeriod_pos m) r
  let e (m : ℕ) := upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
    (TorusRC.positiveEvenPeriod_even m) q (TorusRC.positiveEvenPeriod_pos n)
      (TorusRC.positiveEvenPeriod_pos m)
  let f (m : ℕ) := (1 / (TorusRC.positiveEvenPeriod m : ℝ)) *
    Real.log (SixVertex.Z6Vr c N (TorusRC.positiveEvenPeriod m) r /
      SixVertex.Z6V c N (TorusRC.positiveEvenPeriod m))
  have hNpos : 0 < N := by dsimp [N]; exact TorusRC.positiveEvenPeriod_pos n
  have hc : 0 < c := by dsimp [c]; positivity
  have hZV (m : ℕ) : 0 < SixVertex.Z6V c N (TorusRC.positiveEvenPeriod m) :=
    SixVertex.Z6V_pos hc hNpos (TorusRC.positiveEvenPeriod_pos m)
  have hP (m : ℕ) : 0 < p m := by
    dsimp [p]
    exact upperTailProbability_pos hW12i hW12iii q hq N
      (TorusRC.positiveEvenPeriod m) (TorusRC.positiveEvenPeriod_even n)
      (TorusRC.positiveEvenPeriod_even m) hNpos (TorusRC.positiveEvenPeriod_pos m)
      (by simpa [N] using hr) hr1
  have hE (m : ℕ) : 0 < e m := by
    dsimp [e]
    exact upperLoopExpectation_pos hW12i q hq N (TorusRC.positiveEvenPeriod m)
      (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_even m)
      hNpos (TorusRC.positiveEvenPeriod_pos m)
  have hMseq : Tendsto TorusRC.positiveEvenPeriod atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with m hm
    dsimp [TorusRC.positiveEvenPeriod]
    omega
  have hratioLimit := SixVertex.tendsto_log_Z6V_ratio_eq_Lambda_ratio
    (c := c) (N := N) hc hNpos hr hcenter
  have hlimit : Tendsto f atTop
      (𝓝 (Real.log (SixVertex.Lambda c N r / SixVertex.Lambda c N 0))) := by
    simpa [Function.comp_def, f, N, c] using hratioLimit.comp hMseq
  have hrateBound : ∀ᶠ m : ℕ in atTop,
      f m < -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
    filter_upwards [hTail, hLoop] with m htail hloop
    let M := TorusRC.positiveEvenPeriod m
    have hM : Even M := by dsimp [M]; exact TorusRC.positiveEvenPeriod_even m
    have hMp : 0 < M := by dsimp [M]; exact TorusRC.positiveEvenPeriod_pos m
    have hloop' : |Real.log (e m) / (M : ℝ)| ≤ δ / 2 := by
      simpa [e, M] using hloop
    have htailRate : Real.log (p m) / (M : ℝ) <
        -((r - 1 : ℕ) : ℝ) * ξinv + δ / 2 := by
      simpa [p, M, upperTailProbability, TorusRC.positiveEvenVerticalTailRate] using htail
    have hloopUpper : -Real.log (e m) / (M : ℝ) ≤ δ / 2 := by
      have := (abs_le.mp hloop').1
      simpa [neg_div] using neg_le_neg this
    have hsector := upperTailFactorization hW12i hW12iii q hq N M
      (TorusRC.positiveEvenPeriod_even n) hM hNpos hMp hr (by exact hr1)
    have hratio : SixVertex.Z6Vr c N M r / SixVertex.Z6V c N M ≤
        p m / e m := by
      apply (div_le_iff₀ (hZV m)).2
      simpa [p, e, mul_comm] using hsector
    have hlog : Real.log (SixVertex.Z6Vr c N M r / SixVertex.Z6V c N M) ≤
        Real.log (p m / e m) := Real.log_le_log
          (div_pos (SixVertex.Z6Vr_pos hc hNpos hMp hr) (hZV m)) hratio
    have hlogDiv : Real.log (p m / e m) = Real.log (p m) - Real.log (e m) :=
      Real.log_div (hP m).ne' (hE m).ne'
    have hMcast : 0 < (M : ℝ) := by exact_mod_cast hMp
    have hlog' : Real.log (SixVertex.Z6Vr c N M r / SixVertex.Z6V c N M) ≤
        Real.log (p m) - Real.log (e m) := by
      rw [← hlogDiv]
      exact hlog
    have hrateAux : f m ≤ Real.log (p m) / (M : ℝ) -
        Real.log (e m) / (M : ℝ) := by
      dsimp [f]
      calc
        _ ≤ (1 / (M : ℝ)) * (Real.log (p m) - Real.log (e m)) :=
          mul_le_mul_of_nonneg_left hlog' (by positivity)
        _ = Real.log (p m) / (M : ℝ) - Real.log (e m) / (M : ℝ) := by ring
    dsimp [f]
    calc
      (1 / (M : ℝ)) *
          Real.log (SixVertex.Z6Vr c N M r / SixVertex.Z6V c N M) ≤
        Real.log (p m) / (M : ℝ) - Real.log (e m) / (M : ℝ) := hrateAux
      _ < -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
        have hloopUpper' : -(Real.log (e m) / (M : ℝ)) ≤ δ / 2 := by
          convert hloopUpper using 1; ring
        linarith [htailRate, hloopUpper']
  by_contra hnot
  have hlt : -((r - 1 : ℕ) : ℝ) * ξinv + δ <
      Real.log (SixVertex.Lambda c N r / SixVertex.Lambda c N 0) := lt_of_not_ge hnot
  have hlarge := hlimit.eventually (Ioi_mem_nhds hlt)
  have hfalse : ∀ᶠ m : ℕ in atTop, False := by
    filter_upwards [hlarge, hrateBound] with m hlargeM hrateM
    exact (not_lt_of_ge hrateM.le) hlargeM
  rcases hfalse.exists with ⟨m, hm⟩
  exact hm

/-- The fixed-sector estimate used to take `r → ∞` in the inverse correlation
length upper bound. -/
theorem rc_upper_bound_fixed_r
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW12iii : contract_cor313_iii)
    (hW21eq315 : contract_eq315) (hW21eq316 : contract_eq316)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (hDominance : ∃ Ndom : ℕ, ∀ N : ℕ, 4 ∣ N → Ndom ≤ N →
      SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv))
    (r : ℕ) (hr2 : 2 ≤ r) :
    ∃ S : ℝ, Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
      ((r - 1 : ℕ) : ℝ) * ξinv ≤ (r : ℝ) *
        (Real.arcosh (Real.sqrt q.val / 2) + 2 * S) := by
  classical
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  have hlam : 0 < lam := (PottsDiscontinuity.arcosh_pos_of_gt4 q.val hq).1
  obtain ⟨Sfree, hSfree, hxi, hno, _hboundary⟩ :=
    routeB_free_nonpercolation_and_boundary_decay hW12i hW12ii
      hW21eq315 q hh319 hq μ hμ ξinv hRate
  obtain ⟨Ndom, hdom⟩ := hDominance
  obtain ⟨B, Sbethe, hSbethe, hratio⟩ :=
    apply_17_at_critical_c q.val hq r (by omega)
  have hSbethe_eq : Sbethe = Sfree := tendsto_nhds_unique hSbethe hSfree
  let R : ℝ := lam + 2 * Sbethe
  have hTailEvent := upperTailRateEventually_general hW21eq316 q μ hμ ξinv hRate
    (r := r) (by omega) (δ := 1 / 2) (by norm_num)
  obtain ⟨nTail, hnTail⟩ := Filter.eventually_atTop.1 hTailEvent
  have hzeroSquare := lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno
  obtain ⟨NloopCut, hloopData⟩ :=
    lemma314_limsup_and_one_arm_cutoff q hzeroSquare (1 / 4) (by norm_num)
  let Nloop := NloopCut.val
  let i₀ := max r (max 1 (max nTail (max Nloop Ndom)))
  have hboundEvent : ∀ᶠ i : ℕ in atTop,
      Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
        (4 * (i + B)) r /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          (4 * (i + B)) 0) ≤ -((r - 1 : ℕ) : ℝ) * ξinv + 1 := by
    filter_upwards [Filter.eventually_ge_atTop i₀] with i hi
    let N := 4 * (i + B)
    let n := 2 * (i + B) - 1
    have hperiod : TorusRC.positiveEvenPeriod n = N := by
      dsimp [n, N, TorusRC.positiveEvenPeriod]
      have hnpos : 1 ≤ 2 * (i + B) := by omega
      rw [Nat.sub_add_cancel hnpos]
      omega
    have hi_pos : 1 ≤ i := by dsimp [i₀] at hi; omega
    have hr_i : r ≤ i := by dsimp [i₀] at hi; omega
    have hNdom_i : Ndom ≤ i := by dsimp [i₀] at hi; omega
    have hNloop_i : Nloop ≤ i := by dsimp [i₀] at hi; omega
    have hnTail_i : nTail ≤ i := by dsimp [i₀] at hi; omega
    have hNdom : Ndom ≤ N := by dsimp [N]; omega
    have hNloop : Nloop ≤ N := by dsimp [N]; omega
    have hnTailIndex : nTail ≤ n := by dsimp [n, N]; omega
    have hNdiv : 4 ∣ N := ⟨i + B, rfl⟩
    have hcenter : SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 :=
      hdom N hNdiv hNdom
    have hTail : ∀ᶠ m : ℕ in atTop,
        TorusRC.positiveEvenVerticalTailRate q r n m <
          -((r - 1 : ℕ) : ℝ) * ξinv + 1 / 2 := by
      have hevent := hnTail n hnTailIndex
      filter_upwards [hevent] with m hm
      have hperiod' : TorusRC.positiveEvenPeriod n = N := hperiod
      simpa [hperiod'] using hm
    have hNloopPeriod : Nloop ≤ TorusRC.positiveEvenPeriod n := by
      rw [hperiod]
      exact hNloop
    have hLoop : ∀ᶠ m : ℕ in atTop,
        |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
          (TorusRC.positiveEvenPeriod_even m) q
          (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) /
            (TorusRC.positiveEvenPeriod m : ℝ)| ≤ 1 / 2 := by
      obtain ⟨hlim, harm⟩ := hloopData (TorusRC.positiveEvenPeriod n)
        (TorusRC.positiveEvenPeriod_even n) hNloopPeriod
      have hbounded := windingLoopDensityLogRate_abs_bounded q
        (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_pos n) harm
      exact upperLoopExpectation_abs_log_rate_eventually
        (TorusRC.positiveEvenPeriod_even n) q (TorusRC.positiveEvenPeriod_pos n)
        (1 / 4) hlim hbounded (by norm_num)
    have hfixed := sectorLogRate_le_of_eventual_tail hW12i hW12iii q hq n
      ξinv (1 : ℝ) (r := r)
      (by rw [hperiod]; dsimp [N]; omega)
      (by omega) (by simpa [hperiod] using hcenter) hTail hLoop
    have hratioN : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 =
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 := rfl
    have hfixed' : Real.log (SixVertex.Lambda
        (Real.sqrt (2 + Real.sqrt q.val)) N r /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0) ≤
        -((r - 1 : ℕ) : ℝ) * ξinv + 1 := by
      simpa [hperiod] using hfixed
    simpa [N] using hfixed'
  have hlogLimit : Tendsto (fun i : ℕ => Real.log
      (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) (4 * (i + B)) r /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) (4 * (i + B)) 0))
      atTop (𝓝 (-(r : ℝ) * R)) := by
    have hposLimit : 0 < Real.exp (-(r : ℝ) * R) := Real.exp_pos _
    have h := (Real.continuousAt_log hposLimit.ne').tendsto.comp hratio
    convert h using 1 <;> ext i <;> simp [R, Real.log_exp]
  have hlimitBound : -(r : ℝ) * R ≤ -((r - 1 : ℕ) : ℝ) * ξinv + 1 := by
    by_contra hnot
    have hlt : -((r - 1 : ℕ) : ℝ) * ξinv + 1 < -(r : ℝ) * R := lt_of_not_ge hnot
    have hlarge := hlogLimit.eventually (Ioi_mem_nhds hlt)
    have hfalse : ∀ᶠ i : ℕ in atTop, False := by
      filter_upwards [hlarge, hboundEvent] with i hlargei hboundi
      exact (not_lt_of_ge hboundi) hlargei
    rcases hfalse.exists with ⟨i, hi⟩
    exact hi
  have hforδ : ∀ δ : ℝ, 0 < δ →
      -(r : ℝ) * R ≤ -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
    intro δ hδ
    have hTailEvent' := upperTailRateEventually_general hW21eq316 q μ hμ ξinv hRate
      (r := r) (by omega) (δ := δ / 2) (by linarith)
    obtain ⟨nTail', hnTail'⟩ := Filter.eventually_atTop.1 hTailEvent'
    have hzeroSquare := lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno
    obtain ⟨NloopCut', hloopData'⟩ :=
      lemma314_limsup_and_one_arm_cutoff q hzeroSquare (δ / 4) (by linarith)
    let Nloop' := NloopCut'.val
    let i₁ := max r (max 1 (max nTail' (max Nloop' Ndom)))
    have hboundEvent' : ∀ᶠ i : ℕ in atTop,
        Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          (4 * (i + B)) r /
          SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) (4 * (i + B)) 0) ≤
          -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
      filter_upwards [Filter.eventually_ge_atTop i₁] with i hi
      let N := 4 * (i + B)
      let n := 2 * (i + B) - 1
      have hi_pos : 1 ≤ i := by dsimp [i₁] at hi; omega
      have hr_i : r ≤ i := by dsimp [i₁] at hi; omega
      have hNdom_i : Ndom ≤ i := by dsimp [i₁] at hi; omega
      have hNloop_i : Nloop' ≤ i := by dsimp [i₁] at hi; omega
      have hnTail_i : nTail' ≤ i := by dsimp [i₁] at hi; omega
      have hperiod : TorusRC.positiveEvenPeriod n = N := by
        dsimp [n, N, TorusRC.positiveEvenPeriod]
        rw [Nat.sub_add_cancel (by omega)]
        omega
      have hNdom : Ndom ≤ N := by dsimp [N]; omega
      have hNloop : Nloop' ≤ N := by dsimp [N]; omega
      have hnTailIndex : nTail' ≤ n := by dsimp [n, N]; omega
      have hNdiv : 4 ∣ N := ⟨i + B, rfl⟩
      have hcenter : SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
          SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 :=
        hdom N hNdiv hNdom
      have hTail : ∀ᶠ m : ℕ in atTop,
          TorusRC.positiveEvenVerticalTailRate q r n m <
            -((r - 1 : ℕ) : ℝ) * ξinv + δ / 2 := by
        have hevent := hnTail' n hnTailIndex
        filter_upwards [hevent] with m hm
        simpa [hperiod] using hm
      have hNloopPeriod : Nloop' ≤ TorusRC.positiveEvenPeriod n := by
        rw [hperiod]
        exact hNloop
      have hLoop : ∀ᶠ m : ℕ in atTop,
          |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
            (TorusRC.positiveEvenPeriod_even m) q
            (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) /
              (TorusRC.positiveEvenPeriod m : ℝ)| ≤ δ / 2 := by
        obtain ⟨hlim, harm⟩ := hloopData' (TorusRC.positiveEvenPeriod n)
          (TorusRC.positiveEvenPeriod_even n) hNloopPeriod
        have hbounded := windingLoopDensityLogRate_abs_bounded q
          (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_pos n) harm
        exact upperLoopExpectation_abs_log_rate_eventually
          (TorusRC.positiveEvenPeriod_even n) q (TorusRC.positiveEvenPeriod_pos n)
          (δ / 4) hlim hbounded (by linarith)
      have hfixed := sectorLogRate_le_of_eventual_tail hW12i hW12iii q hq n
        ξinv δ (r := r) (by rw [hperiod]; dsimp [N]; omega) (by omega)
        (by simpa [hperiod] using hcenter) hTail hLoop
      simpa [N, hperiod] using hfixed
    have hlimitBound' : -(r : ℝ) * R ≤ -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
      by_contra hnot
      have hlt : -((r - 1 : ℕ) : ℝ) * ξinv + δ < -(r : ℝ) * R := lt_of_not_ge hnot
      have hlarge := hlogLimit.eventually (Ioi_mem_nhds hlt)
      have hfalse : ∀ᶠ i : ℕ in atTop, False := by
        filter_upwards [hlarge, hboundEvent'] with i hlargei hboundi
        exact (not_lt_of_ge hboundi) hlargei
      rcases hfalse.exists with ⟨i, hi⟩
      exact hi
    exact hlimitBound'
  have hfinal : ((r - 1 : ℕ) : ℝ) * ξinv ≤ (r : ℝ) * R := by
    by_contra hnot
    have hgap : -((r - 1 : ℕ) : ℝ) * ξinv < -(r : ℝ) * R := by
      dsimp [R] at hnot ⊢
      nlinarith
    let δ := (-(r : ℝ) * R - (-((r - 1 : ℕ) : ℝ) * ξinv)) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hbound := hforδ δ hδ
    dsimp [δ] at hbound
    linarith
  exact ⟨Sbethe, hSbethe, by simpa [R] using hfinal⟩

private theorem firstSectorStrict_eventually
    (q : ℝ) (hq : 4 < q) :
    ∃ Nfirst : ℕ, ∀ N : ℕ, 4 ∣ N → Nfirst ≤ N →
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 1 <
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 := by
  let lam := Real.arcosh (Real.sqrt q / 2)
  obtain ⟨B, S, hS, hratio⟩ := apply_17_at_critical_c q hq 1 (by omega)
  have hlam : 0 < lam := by
    dsimp [lam]
    apply Real.arcosh_pos
    have hqpos : 0 < q := by linarith
    have hsqrt : 2 < Real.sqrt q := by
      have hs := Real.sq_sqrt (le_of_lt hqpos)
      nlinarith [Real.sqrt_nonneg q]
    linarith
  obtain ⟨S₀, T, hS₀, hT, hpositive, hidentity⟩ :=
    PottsDiscontinuity.identity44 lam hlam
  have hS₀' : Tendsto (PottsDiscontinuity.altTanhPartial lam)
      atTop (𝓝 S₀) := by
    change Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S₀)
    exact hS₀
  have hSS : S = S₀ := tendsto_nhds_unique hS hS₀'
  have hRpos : 0 < lam + 2 * S := by rw [hSS]; exact hpositive
  have hexp : Real.exp (-(lam + 2 * S)) < 1 := by
    apply (Real.exp_lt_one_iff).2
    linarith
  have hexp' : Real.exp (-(1 : ℝ) *
      (Real.arcosh (Real.sqrt q / 2) + 2 * S)) < 1 := by
    have harg : -(1 : ℝ) *
        (Real.arcosh (Real.sqrt q / 2) + 2 * S) = -(lam + 2 * S) := by
      dsimp [lam]
      ring
    rw [harg]
    exact hexp
  have hratioEvent : ∀ᶠ i : ℕ in atTop,
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) 1 /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) 0 < 1 := by
    have hexpLimit : Real.exp (-(↑(1 : ℕ) : ℝ) *
        (Real.arcosh (Real.sqrt q / 2) + 2 * S)) < 1 := by
      simpa using hexp'
    exact hratio.eventually (Iio_mem_nhds hexpLimit)
  obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.1 hratioEvent
  refine ⟨4 * (i₀ + B), ?_⟩
  intro N hdiv hlarge
  obtain ⟨k, hk⟩ := hdiv
  have hklarge : i₀ + B ≤ k := by
    have hle : 4 * (i₀ + B) ≤ 4 * k := by simpa [hk] using hlarge
    omega
  let i := k - B
  have hi : i₀ ≤ i := by dsimp [i]; omega
  have hNrepr : N = 4 * (i + B) := by
    rw [hk]
    dsimp [i]
    omega
  have hratioLt := hi₀ i hi
  have hcenterPos : 0 < SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 := by
    apply SixVertex.Lambda_pos
    · positivity
    · omega
  have hlt : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 1 /
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 < 1 := by
    simpa [hNrepr] using hratioLt
  have hfirst : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 1 <
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 :=
    (div_lt_one hcenterPos).1 hlt
  exact hfirst

/-- The repaired dominance gap: for all sufficiently large widths divisible by four,
the centered six-vertex block has the largest Perron root. -/
theorem rc_dominance_for_large_width
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW12iii : contract_cor313_iii)
    (hW21eq315 : contract_eq315) (hW21eq316 : contract_eq316)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, 4 ∣ N → N₀ ≤ N →
      SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 := by
  obtain ⟨S, hS, hxi, hno, _hboundary⟩ :=
    routeB_free_nonpercolation_and_boundary_decay hW12i hW12ii
      hW21eq315 q hh319 hq μ hμ ξinv hRate
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  have hlam : 0 < lam := (PottsDiscontinuity.arcosh_pos_of_gt4 q.val hq).1
  obtain ⟨S₀, T, hS₀, hT, hpositive, hidentity⟩ :=
    PottsDiscontinuity.identity44 lam hlam
  have hS₀' : Tendsto (PottsDiscontinuity.altTanhPartial lam)
      atTop (𝓝 S₀) := by
    change Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S₀)
    exact hS₀
  have hSS : S = S₀ := tendsto_nhds_unique hS hS₀'
  have hRpositive : 0 < lam + 2 * S := by rw [hSS]; exact hpositive
  have hxiPos : 0 < ξinv := lt_of_lt_of_le hRpositive (by simpa [lam] using hxi)
  obtain ⟨Nfirst, hfirstEvent⟩ := firstSectorStrict_eventually q.val hq
  have htailEvent := upperTailRateEventually hW21eq316 q μ hμ ξinv hRate hxiPos
  obtain ⟨nTail, hnTail⟩ := Filter.eventually_atTop.1 htailEvent
  have hzeroSquare := lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno
  obtain ⟨NloopCut, hloopData⟩ :=
    lemma314_limsup_and_one_arm_cutoff q hzeroSquare (ξinv / 64) (by positivity)
  let Nloop := NloopCut.val
  let n₀ := max nTail Nloop
  let N₀ := max 4 (max (4 * (n₀ + 1)) Nfirst)
  refine ⟨N₀, ?_⟩
  intro N hdiv hlarge
  obtain ⟨k, hk⟩ := hdiv
  let n := 2 * k - 1
  have hNpos : 0 < N := by dsimp [N₀] at hlarge; omega
  have hperiod : TorusRC.positiveEvenPeriod n = N := by
    dsimp [n, TorusRC.positiveEvenPeriod]
    rw [hk]
    have hkpos : 1 ≤ 2 * k := by omega
    rw [Nat.sub_add_cancel hkpos]
    omega
  have hnTailIndex : nTail ≤ n := by
    dsimp [n₀, n] at hlarge ⊢
    dsimp [N₀] at hlarge
    omega
  have hNloop : Nloop ≤ TorusRC.positiveEvenPeriod n := by
    rw [hperiod]
    dsimp [N₀] at hlarge
    omega
  have hN : Even N := by
    refine ⟨2 * k, ?_⟩
    rw [hk]
    ring
  have hdivN : 4 ∣ N := ⟨k, hk⟩
  have hfirst : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 1 <
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 := by
    apply hfirstEvent N hdivN
    dsimp [N₀] at hlarge
    omega
  have hTail : ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q 2 n m < -3 * ξinv / 4 :=
    hnTail n hnTailIndex
  have hLoop : ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
        (TorusRC.positiveEvenPeriod_even m) q
        (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ ξinv / 32 := by
    obtain ⟨hlim, harm⟩ := hloopData (TorusRC.positiveEvenPeriod n)
      (TorusRC.positiveEvenPeriod_even n) hNloop
    have hbounded := windingLoopDensityLogRate_abs_bounded q
      (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_pos n) harm
    exact upperLoopExpectation_abs_log_rate_eventually
      (TorusRC.positiveEvenPeriod_even n) q (TorusRC.positiveEvenPeriod_pos n)
      (ξinv / 64) hlim hbounded (by linarith)
  have hbulk : ∀ r : ℕ, 2 ≤ r → r ≤ N / 2 →
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r ≤
        Real.exp (-(ξinv / 2)) * SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N := by
    intro r hr2 hr
    have hgap := upperDominanceGap_fixedIndex hW12i hW12iii q hq ξinv hxiPos n Nloop
      hNloop hTail hLoop (by simpa [hperiod] using hr) hr2
    have hLrPos : 0 < SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r := by
      exact SixVertex.Lambda_pos (by positivity) hr
    have hLmaxPos : 0 < SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N :=
      SixVertex.LambdaMax_pos (by positivity)
    have hgapN : Real.log (SixVertex.Lambda
        (Real.sqrt (2 + Real.sqrt q.val)) N r) ≤
        Real.log (SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N) - ξinv / 2 := by
      simpa [hperiod] using hgap
    have hexp := Real.exp_le_exp.mpr hgapN
    have hlogToRoot : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r ≤
        Real.exp (Real.log (SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N) - ξinv / 2) := by
      rw [Real.exp_log hLrPos] at hexp
      exact hexp
    calc
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r ≤
          Real.exp (Real.log (SixVertex.LambdaMax
            (Real.sqrt (2 + Real.sqrt q.val)) N) - ξinv / 2) := hlogToRoot
      _ = Real.exp (-(ξinv / 2)) * SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N := by
        rw [Real.exp_sub, Real.exp_log hLmaxPos]
        rw [Real.exp_neg]
        ring
  have hmax := SixVertex.LambdaMax_eq_Lambda0_of_dominance
    (by positivity) hN hNpos (by positivity) hbulk hfirst
  simpa [hperiod] using hmax

/-- The upper estimate for the inverse correlation length follows from the
fixed-sector bounds after the repaired dominant-eigenvalue identification. -/
theorem rc_xi_inverse_le_critical_rate
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW12iii : contract_cor313_iii)
    (hW21eq315 : contract_eq315) (hW21eq316 : contract_eq316)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv)) :
    ∃ S : ℝ, Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
      ξinv ≤ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  obtain ⟨Ndom, hdom⟩ := rc_dominance_for_large_width
    hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq μ hμ ξinv hRate
  obtain ⟨_, S, hS, _hratio⟩ := apply_17_at_critical_c q.val hq 1 (by omega)
  have hbound (r : ℕ) (hr : 2 ≤ r) :
      ((r - 1 : ℕ) : ℝ) * ξinv ≤ (r : ℝ) *
        (Real.arcosh (Real.sqrt q.val / 2) + 2 * S) := by
    obtain ⟨S', hS', hsector⟩ := rc_upper_bound_fixed_r
      hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq
      ⟨Ndom, hdom⟩ μ hμ ξinv hRate r hr
    have hS'eq : S' = S := tendsto_nhds_unique hS' hS
    simpa [hS'eq] using hsector
  let R := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  have hR : ξinv ≤ R := by
    by_contra hnot
    have hgap : 0 < ξinv - R := by linarith
    have hsmall : ∀ᶠ n : ℕ in atTop,
        (1 / (n : ℝ)) * R < (ξinv - R) / 2 := by
      have hzero := tendsto_one_div_atTop_nhds_zero_nat.mul_const R
      exact hzero.eventually (Iio_mem_nhds (by linarith))
    have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_gt_atTop 0
    obtain ⟨n, hnsmall, hnpositive⟩ := (hsmall.and hpositive).exists
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpositive
    have hsector := hbound (n + 1) (by omega)
    have hsector' : (n : ℝ) * ξinv ≤ ((n : ℝ) + 1) * R := by
      have hsub : (n + 1) - 1 = n := by omega
      rw [hsub] at hsector
      norm_num [Nat.cast_add] at hsector ⊢
      simpa [R] using hsector
    have hdiv : ξinv ≤ (((n : ℝ) + 1) * R) / (n : ℝ) :=
      (le_div_iff₀ hnR).2 (by nlinarith [hsector'])
    have hdivEq : (((n : ℝ) + 1) * R) / (n : ℝ) =
        R + (1 / (n : ℝ)) * R := by
      field_simp [ne_of_gt hnR]
    rw [hdivEq] at hdiv
    linarith
  exact ⟨S, hS, by simpa [R] using hR⟩

end PottsDiscontinuity.RCMProof

