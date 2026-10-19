module

public import PottsDiscontinuity.RCMProof.BetheAssembly
public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.RCMProof.ExactOneWitness
public import PottsDiscontinuity.SixVertex.Sec33Ratios
public import PottsDiscontinuity.TorusTopology.UnitWindingContract

/-!
# The lower bound on the inverse correlation length

The first lemma converts the exact-one-winding probability into a six-vertex
sector ratio. The fixed factor `q^2` absorbs the net indicator without a
separate no-net assertion.
-/

@[expose] public section

open Finset Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open Torus

noncomputable def lowerLoopFactor {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) : ℝ :=
  Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A : ℝ) *
    Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ))

private theorem lowerLoopFactor_le_one {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) : lowerLoopFactor hN hM q hNp hMp A ≤ 1 := by
  have hqpos : 0 < q.val := by linarith
  have hsqrt : 2 < Real.sqrt q.val := by
    have hs := Real.sq_sqrt (le_of_lt hqpos)
    have hn := Real.sqrt_nonneg q.val
    nlinarith
  have hbase : 0 ≤ 2 / Real.sqrt q.val ∧ 2 / Real.sqrt q.val ≤ 1 := by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      linarith
  have hnet : 0 ≤ (Torus.rcNetIndicator hN hM A : ℝ) := by positivity
  have hfactor₁ := Real.rpow_le_one hbase.1 hbase.2
    (show 0 ≤ (TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A : ℝ) by positivity)
  have hfactor₂ := Real.rpow_le_one_of_one_le_of_nonpos
    q.property (neg_nonpos.mpr hnet)
  have hfactor₂nonneg : 0 ≤ Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) :=
    Real.rpow_nonneg (le_of_lt hqpos) _
  unfold lowerLoopFactor
  calc
    _ ≤ 1 * Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactor₁ hfactor₂nonneg
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hfactor₂ (by norm_num)
    _ = 1 := by ring

private theorem lowerLoopFactor_ge_qsq_inv {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (hU : rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1) :
    4 / q.val ^ 2 ≤ lowerLoopFactor hN hM q hNp hMp A := by
  have hqpos : 0 < q.val := by linarith
  have hqone : 1 ≤ q.val := le_trans (by norm_num) q.property
  have hsqrt : 0 < Real.sqrt q.val := Real.sqrt_pos.2 hqpos
  have hcount := TorusTopology.windingLoopCount_eq_two_of_U_eq_one
    hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A hU
  have hnet : Torus.rcNetIndicator hN hM A ≤ 1 := by
    unfold Torus.rcNetIndicator
    split_ifs <;> omega
  have hnetcast : (Torus.rcNetIndicator hN hM A : ℝ) ≤ 1 := by exact_mod_cast hnet
  have hpow : Real.rpow q.val (-1 : ℝ) ≤
      Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hqone
    linarith
  have hpow' : 1 / q.val ≤
      Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) := by
    simpa [Real.rpow_neg_one] using hpow
  have hsq : Real.rpow (2 / Real.sqrt q.val) (2 : ℝ) = 4 / q.val := by
    have hsquare : Real.sqrt q.val ^ 2 = q.val := Real.sq_sqrt (le_of_lt hqpos)
    calc
      Real.rpow (2 / Real.sqrt q.val) (2 : ℝ) =
          (2 / Real.sqrt q.val) ^ (2 : ℕ) := Real.rpow_natCast _ _
      _ = 4 / q.val := by
        rw [div_pow, hsquare]
        norm_num
  unfold lowerLoopFactor
  rw [hcount]
  have hsq' : Real.rpow (2 / Real.sqrt q.val) ((2 : ℕ) : ℝ) = 4 / q.val := by
    simpa using hsq
  rw [hsq']
  have hmul := mul_le_mul_of_nonneg_left hpow' (show 0 ≤ 4 / q.val by positivity)
  calc
    4 / q.val ^ 2 = (4 / q.val) * (1 / q.val) := by
      field_simp
    _ ≤ (4 / q.val) * Real.rpow q.val
          (-(Torus.rcNetIndicator hN hM A : ℝ)) := hmul
    _ = (4 / q.val) * Real.rpow q.val
          (-(Torus.rcNetIndicator hN hM A : ℝ)) := rfl

theorem exactOneProbability_le_qsq_mul_sector_ratio
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) :
    TorusRC.torusRCProbability hN hM q
      {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1} ≤
      q.val ^ 2 * (SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 /
        SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M) := by
  classical
  let E : Set (RCConfig N M) :=
    {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1}
  let w : RCConfig N M → ℝ := Torus.torusRCWeight hN hM q
  let f : RCConfig N M → ℝ := lowerLoopFactor hN hM q hNp hMp
  let C : ℝ := Torus.torusNormalization q N M
  let Z0 : ℝ := SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M
  let Z1 : ℝ := SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1
  have hC : 0 < C := by
    dsimp [C]
    exact Torus.torusNormalization_pos q N M
  have hZ0 : 0 < Z0 := by
    dsimp [Z0]
    apply SixVertex.Z6V_pos
    · positivity
    · exact hNp
    · exact hMp
  have hZ1 : 0 < Z1 := by
    dsimp [Z1]
    apply SixVertex.Z6Vr_pos
    · positivity
    · exact hNp
    · exact hMp
    · rcases hN with ⟨k, hk⟩
      omega
  have htotalContract := hW12i q hq N M hN hM hNp hMp
  change (∑ A : RCConfig N M, w A * f A) = C * Z0 at htotalContract
  have honeContract := hW12ii q hq N M hN hM hNp hMp
  change (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A * f A) ≤
      4 * C * Z1 at honeContract
  have hpart : TorusRC.torusRCPartition hN hM q = ∑ A : RCConfig N M, w A := by
    rfl
  have hden : C * Z0 ≤ TorusRC.torusRCPartition hN hM q := by
    rw [hpart, ← htotalContract]
    apply Finset.sum_le_sum
    intro A hA
    have hf := lowerLoopFactor_le_one hN hM q hq hNp hMp A
    have hw : 0 ≤ w A := (TorusRC.torusRCWeight_pos hN hM q A).le
    dsimp [w, f] at *
    exact mul_le_of_le_one_right hw hf
  have hnum :
      (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) ≤
        (q.val ^ 2 / 4) *
          (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A * f A) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    have hU : rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1 := by
      simpa [E] using hA
    have hf := lowerLoopFactor_ge_qsq_inv hN hM q hq hNp hMp A hU
    have hw : 0 ≤ w A := (TorusRC.torusRCWeight_pos hN hM q A).le
    dsimp [w, f]
    have hcoef : 0 < q.val ^ 2 / 4 := by positivity
    have hcoef' : 1 ≤ (q.val ^ 2 / 4) * lowerLoopFactor hN hM q hNp hMp A := by
      calc
        1 = (q.val ^ 2 / 4) * (4 / q.val ^ 2) := by
          field_simp
        _ ≤ (q.val ^ 2 / 4) * lowerLoopFactor hN hM q hNp hMp A :=
          mul_le_mul_of_nonneg_left hf hcoef.le
    calc
      w A = w A * 1 := by ring
      _ ≤ w A * ((q.val ^ 2 / 4) * lowerLoopFactor hN hM q hNp hMp A) :=
        mul_le_mul_of_nonneg_left hcoef' hw
      _ = (q.val ^ 2 / 4) * (w A * lowerLoopFactor hN hM q hNp hMp A) := by ring
  have hnum' :
      (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) ≤
        q.val ^ 2 * C * Z1 := by
    calc
      _ ≤ (q.val ^ 2 / 4) *
          (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A * f A) := hnum
      _ ≤ (q.val ^ 2 / 4) * (4 * C * Z1) := by
        exact mul_le_mul_of_nonneg_left honeContract (by positivity)
      _ = q.val ^ 2 * C * Z1 := by ring
  have hprobEq : TorusRC.torusRCProbability hN hM q E =
      (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) /
        TorusRC.torusRCPartition hN hM q := by
    rw [TorusRC.torusRCProbability_eq_sum]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp_rw [TorusRC.torusRCMass, w]
    rw [← Finset.sum_div]
  rw [show TorusRC.torusRCProbability hN hM q E =
      TorusRC.torusRCProbability hN hM q
        {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1} from by rfl]
  rw [hprobEq]
  have hquot₁ :
      (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) /
          TorusRC.torusRCPartition hN hM q ≤
        (q.val ^ 2 * C * Z1) / TorusRC.torusRCPartition hN hM q := by
    apply div_le_div_of_nonneg_right hnum'
    exact le_of_lt (TorusRC.torusRCPartition_pos hN hM q)
  have hquot₂ :
      (q.val ^ 2 * C * Z1) / TorusRC.torusRCPartition hN hM q ≤
        (q.val ^ 2 * C * Z1) / (C * Z0) := by
    apply div_le_div_of_nonneg_left
    · positivity
    · exact mul_pos hC hZ0
    · exact hden
  have hquot :
      (q.val ^ 2 * C * Z1) / (C * Z0) = q.val ^ 2 * (Z1 / Z0) := by
    field_simp [hC.ne', hZ0.ne']
  simpa [E, Z0, Z1, hquot] using hquot₁.trans hquot₂

private theorem Z6Vr_le_Z6V_of_pos {c : ℝ} {N M : ℕ}
    (hc : 0 < c) (hN : 0 < N) (hM : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) : SixVertex.Z6Vr c N M r ≤ SixVertex.Z6V c N M := by
  have hEq : SixVertex.Z6Vr c N M r =
      SixVertex.Z6Vn c N M (N / 2 - r) := by
    rw [SixVertex.Z6Vr_eq_trace_block hN hM c hr,
      SixVertex.Z6Vn_eq_trace_block hN hM c]
  rw [hEq]
  exact SixVertex.Z6Vn_le_Z6V hc.le hM (by omega)

private theorem lowerExactOneRate_liminf_le_lambda_gap
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N : ℕ) (hN : Even N)
    (hNlarge : 8 ≤ N) (hNdiv : 8 ∣ N)
    (δ : ℝ) (hδ : 0 < δ) :
    Filter.liminf (TorusRC.torusRCUOneRateE hN q) Filter.atTop ≤
      ((Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          N 1) -
        Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          N 0) + δ : ℝ) : EReal) := by
  have hNpos : 0 < N := by obtain ⟨k, hk⟩ := hN; omega
  have hMseq : Filter.Tendsto TorusRC.positiveEvenPeriod Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with m hm
    simp [TorusRC.positiveEvenPeriod]
    omega
  have hMreal : Filter.Tendsto (fun m : ℕ =>
      (TorusRC.positiveEvenPeriod m : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hMseq
  have hMlarge : ∀ᶠ m : ℕ in Filter.atTop,
      N / 2 < TorusRC.positiveEvenPeriod m := by
    exact hMseq.eventually (Filter.eventually_gt_atTop (N / 2))
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let gap : ℝ := Real.log (SixVertex.Lambda c N 1) -
    Real.log (SixVertex.Lambda c N 0)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsectorLimsup : Filter.limsup (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) Filter.atTop ≤ gap := by
    dsimp [gap]
    apply SixVertex.limsup_log_Z6V_ratio_le_center hc hNpos
    omega
  have hsectorBound : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun M : ℕ => (1 / (M : ℝ)) *
        Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) := by
    apply Filter.isBoundedUnder_of_eventually_le
    filter_upwards [Filter.eventually_gt_atTop 0] with M hM
    have hMpos : 0 < M := hM
    have hZnum : 0 < SixVertex.Z6Vr c N M 1 := by
      apply SixVertex.Z6Vr_pos hc hNpos hMpos
      omega
    have hZden : 0 < SixVertex.Z6V c N M := SixVertex.Z6V_pos hc hNpos hMpos
    have hratio : 0 < SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M :=
      div_pos hZnum hZden
    have hratioLe : SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M ≤ 1 := by
      apply (div_le_one hZden).2
      exact Z6Vr_le_Z6V_of_pos hc hNpos hMpos (by omega)
    have hlog : Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) ≤ 0 :=
      Real.log_nonpos hratio.le hratioLe
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog
  have hsectorEventually (η : ℝ) (hη : 0 < η) :
      ∀ᶠ M : ℕ in Filter.atTop,
        (1 / (M : ℝ)) *
          Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) < gap + η := by
    have hlt : Filter.limsup (fun M : ℕ => (1 / (M : ℝ)) *
        Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) Filter.atTop <
        gap + η := lt_of_le_of_lt hsectorLimsup (by linarith)
    exact Filter.eventually_lt_of_limsup_lt hlt hsectorBound
  have hsectorEventualOnM := hMseq.eventually (hsectorEventually (δ / 2) (by linarith))
  have hconst : Filter.Tendsto (fun m : ℕ => Real.log (q.val ^ 2) /
      (TorusRC.positiveEvenPeriod m : ℝ)) Filter.atTop (𝓝 0) :=
    hMreal.const_div_atTop (Real.log (q.val ^ 2))
  have hconstEventual : ∀ᶠ m : ℕ in Filter.atTop,
      Real.log (q.val ^ 2) / (TorusRC.positiveEvenPeriod m : ℝ) < δ / 2 :=
    hconst.eventually (Iio_mem_nhds (by linarith))
  have hrateEventual : ∀ᶠ m : ℕ in Filter.atTop,
      TorusRC.torusRCUOneRateE hN q m ≤ (gap + δ : EReal) := by
    filter_upwards [hMlarge, hsectorEventualOnM, hconstEventual] with m hmLarge hsector hconstm
    let M := TorusRC.positiveEvenPeriod m
    have hMpos : 0 < M := by dsimp [M]; exact TorusRC.positiveEvenPeriod_pos m
    have hM : Even M := by dsimp [M]; exact TorusRC.positiveEvenPeriod_even m
    have hprob := exactOneProbability_le_qsq_mul_sector_ratio
      hW12i hW12ii q hq N M hN hM hNpos hMpos
    have hprobPos := exactOneProbability_pos_of_large_eight_width
      q hN hM hNdiv hNlarge hMpos (by simpa [M] using hmLarge)
    have hZnum : 0 < SixVertex.Z6Vr c N M 1 := by
      apply SixVertex.Z6Vr_pos hc hNpos hMpos
      omega
    have hZden : 0 < SixVertex.Z6V c N M := SixVertex.Z6V_pos hc hNpos hMpos
    have hratio : 0 < SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M :=
      div_pos hZnum hZden
    have hq2 : 0 < q.val ^ 2 := by positivity
    have hlog := Real.log_le_log hprobPos hprob
    rw [Real.log_mul hq2.ne' hratio.ne'] at hlog
    have hrealRate : Real.log (TorusRC.torusRCProbability hN hM q
        {A | rcVerticalWinding hN hM ⟨0, TorusRC.positiveEvenPeriod_pos m⟩ A = 1}) /
          (M : ℝ) ≤
        (1 / (M : ℝ)) * Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) +
          Real.log (q.val ^ 2) / (M : ℝ) := by
      have hMposR : 0 < (M : ℝ) := by exact_mod_cast hMpos
      calc
        _ ≤ (Real.log (q.val ^ 2) +
            Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) / (M : ℝ) :=
          div_le_div_of_nonneg_right hlog (Nat.cast_nonneg M)
        _ = _ := by rw [add_div]; ring
    have hstrict : (1 / (M : ℝ)) *
          Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) +
          Real.log (q.val ^ 2) / (M : ℝ) < gap + δ := by linarith
    apply EReal.coe_le_coe_iff.mpr
    change Real.log (TorusRC.torusRCProbability
        hN (TorusRC.positiveEvenPeriod_even m) q
        {A | rcVerticalWinding hN
          (TorusRC.positiveEvenPeriod_even m) ⟨0, TorusRC.positiveEvenPeriod_pos m⟩ A = 1}) /
        (TorusRC.positiveEvenPeriod m : ℝ) ≤ gap + δ
    dsimp [M] at hrealRate
    exact hrealRate.trans hstrict.le
  exact Filter.liminf_le_of_frequently_le' hrateEventual.frequently

private theorem freeLimitRate_eq_torusRC_inverseCorrelationLength
    (q : Set.Ici (1 : ℝ))
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) /
        (n : ℝ)) Filter.atTop (nhds ξinv)) :
    ξinv = TorusRC.inverseCorrelationLength q := by
  obtain ⟨aInf, _, hrot, hdiag⟩ :=
    CorrLength.rotated_correlation_rate_exists_for_limit (FK.criticalParameters q) μ hμ
  have hxi : ξinv = aInf / 2 := tendsto_nhds_unique hRate hdiag
  have hrot' : Filter.Tendsto (fun n : ℕ =>
      -Real.log ((CorrLength.rotatedDiagonalConnectionProbability
        (TorusRC.torusRCBridgeParameters q) n : NNReal) : ℝ) /
        ((2 * n : ℕ) : ℝ)) Filter.atTop (nhds (aInf / 2)) := by
    simpa [TorusRC.torusRCBridgeParameters, TorusRC.torusRCFKParameters,
      FK.criticalParameters] using hrot
  have hcanonical := TorusRC.tendsto_inverseCorrelationLength q
  have hcan : aInf / 2 = TorusRC.inverseCorrelationLength q :=
    tendsto_nhds_unique hrot' hcanonical
  exact hxi.trans hcan

/-- The exact-one-winding lower bound (3.24), using the provider contracts for
Corollary 3.13(i)–(ii) and equation (3.15) (`contract_cor313_i`, `contract_cor313_ii`,
`contract_eq315`). The quantity `R` is kept in its source form `λ + 2S`. -/
theorem xi_inverse_ge_critical_rate
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW21 : contract_eq315)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) /
        (n : ℝ)) Filter.atTop (nhds ξinv)) :
    ∃ S : ℝ,
      Filter.Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2)))
        Filter.atTop (nhds S) ∧
      ξinv ≥ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  obtain ⟨B, S, hS, hroot⟩ := apply_17_at_critical_c q.val hq 1 (by omega)
  let R : ℝ := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let idx : ℕ → ℕ := fun j => 2 * (j + 1) + B % 2
  let nSeq : ℕ → ℕ := fun j => 2 * (idx j + B) - 1
  have hidxEven (j : ℕ) : Even (idx j + B) := by
    refine ⟨j + 1 + B / 2 + B % 2, ?_⟩
    dsimp [idx]
    omega
  have hperiod (j : ℕ) : TorusRC.positiveEvenPeriod (nSeq j) =
      4 * (idx j + B) := by
    have hpos : 1 ≤ 2 * (idx j + B) := by dsimp [idx]; omega
    simp [nSeq, TorusRC.positiveEvenPeriod, Nat.sub_add_cancel hpos]
    omega
  have hwidthLarge (j : ℕ) : 8 ≤ 4 * (idx j + B) := by
    dsimp [idx]
    omega
  have hwidthDiv (j : ℕ) : 8 ∣ TorusRC.positiveEvenPeriod (nSeq j) := by
    rw [hperiod]
    obtain ⟨k, hk⟩ := hidxEven j
    refine ⟨k, ?_⟩
    rw [hk]
    omega
  have hidxAtTop : Filter.Tendsto idx Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with j hj
    dsimp [idx]
    omega
  have hnSeqAtTop : Filter.Tendsto nSeq Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with j hj
    dsimp [nSeq, idx]
    omega
  have hrootSeq : Filter.Tendsto
      (fun j : ℕ => SixVertex.Lambda c (4 * (idx j + B)) 1 /
        SixVertex.Lambda c (4 * (idx j + B)) 0)
      Filter.atTop (nhds (Real.exp (-R))) := by
    convert hroot.comp hidxAtTop using 1
    · rfl
    · simp only [R]
      congr 1
      ring_nf
  have hc : 0 < c := by dsimp [c]; positivity
  let ratioSeq : ℕ → ℝ := fun j =>
    SixVertex.Lambda c (4 * (idx j + B)) 1 /
      SixVertex.Lambda c (4 * (idx j + B)) 0
  have hratioPos (j : ℕ) : 0 < ratioSeq j := by
    have hsize : 1 ≤ (4 * (idx j + B)) / 2 := by
      have := hwidthLarge j
      omega
    exact div_pos (SixVertex.Lambda_pos hc hsize)
      (SixVertex.Lambda_pos hc (by omega))
  have hlogRatio : Filter.Tendsto (fun j => Real.log (ratioSeq j))
      Filter.atTop (nhds (-R)) := by
    have h := (Real.continuousAt_log (Real.exp_pos (-R)).ne').tendsto.comp hrootSeq
    convert h using 1
    · rfl
    · simp [Real.log_exp]
  let gapSeq : ℕ → ℝ := fun j =>
    Real.log (SixVertex.Lambda c (4 * (idx j + B)) 1) -
      Real.log (SixVertex.Lambda c (4 * (idx j + B)) 0)
  have hgapEq (j : ℕ) : gapSeq j = Real.log (ratioSeq j) := by
    dsimp [gapSeq, ratioSeq]
    rw [Real.log_div (SixVertex.Lambda_pos hc (by
      have := hwidthLarge j
      omega)).ne' (SixVertex.Lambda_pos hc (by omega)).ne']
  have hgap : Filter.Tendsto gapSeq Filter.atTop (nhds (-R)) := by
    convert hlogRatio using 1
    funext j
    exact hgapEq j
  have hgapEventually (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j : ℕ in Filter.atTop, gapSeq j < -R + ε := by
    exact hgap.eventually (Iio_mem_nhds (by linarith))
  let outerRate8 : ℕ → EReal := fun k =>
    Filter.liminf (TorusRC.torusRCUOneRateE
      (TorusRC.eightfoldPeriod_even k) q) Filter.atTop
  let kSeq : ℕ → ℕ := fun j => (idx j + B) / 2 - 1
  have hkSeqAtTop : Filter.Tendsto kSeq Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with j hj
    have hbound : 2 * (j + 1) ≤ idx j + B := by
      dsimp [idx]
      omega
    have hdiv : j + 1 ≤ (idx j + B) / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by omega)
    have hjk : j ≤ kSeq j := by dsimp [kSeq]; omega
    exact hj.trans hjk
  have hwidth8 (j : ℕ) : TorusRC.eightfoldPeriod (kSeq j) =
      TorusRC.positiveEvenPeriod (nSeq j) := by
    dsimp [TorusRC.eightfoldPeriod, kSeq]
    rw [hperiod]
    obtain ⟨k, hk⟩ := hidxEven j
    rw [hk]
    have hlarge : 8 ≤ 4 * (k + k) := by
      have h := hwidthLarge j
      rw [hk] at h
      exact h
    have hkpos : 0 < k := by omega
    have hdiv : (k + k) / 2 = k := by omega
    rw [hdiv]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    omega
  have houterBound (ε : ℝ) (hε : 0 < ε) :
      Filter.liminf outerRate8 Filter.atTop ≤ ((-R + ε : ℝ) : EReal) := by
    have hnear := hgapEventually (ε / 2) (by linarith)
    have hinnerEventually : ∀ᶠ j : ℕ in Filter.atTop,
        outerRate8 (kSeq j) ≤ ((-R + ε : ℝ) : EReal) := by
      filter_upwards [hnear] with j hj
      have hfixed := lowerExactOneRate_liminf_le_lambda_gap
        hW12i hW12ii q hq (TorusRC.eightfoldPeriod (kSeq j))
        (TorusRC.eightfoldPeriod_even (kSeq j)) (by
          dsimp [TorusRC.eightfoldPeriod]
          omega) (TorusRC.eightfoldPeriod_dvd (kSeq j)) (ε / 2) (by linarith)
      have hvalue :
          Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
              (TorusRC.eightfoldPeriod (kSeq j)) 1) -
            Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
              (TorusRC.eightfoldPeriod (kSeq j)) 0) + ε / 2 =
          gapSeq j + ε / 2 := by
        rw [hwidth8 j, hperiod]
      have hfixed' : outerRate8 (kSeq j) ≤
          ((gapSeq j + ε / 2 : ℝ) : EReal) := by
        dsimp [outerRate8]
        rw [hvalue] at hfixed
        exact hfixed
      have hupper : gapSeq j + ε / 2 ≤ -R + ε := by linarith
      have hupperE : ((gapSeq j + ε / 2 : ℝ) : EReal) ≤
          ((-R + ε : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hupper
      exact hfixed'.trans hupperE
    have hfrequently : ∃ᶠ n : ℕ in Filter.atTop,
        outerRate8 n ≤ ((-R + ε : ℝ) : EReal) := by
      rw [Filter.frequently_atTop']
      intro K
      obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hinnerEventually
      have hKevent := hkSeqAtTop.eventually (Filter.eventually_gt_atTop K)
      obtain ⟨Jk, hJk⟩ := Filter.eventually_atTop.1 hKevent
      let j := max J Jk
      have hJle : J ≤ j := by dsimp [j]; exact Nat.le_max_left _ _
      have hJkle : Jk ≤ j := by dsimp [j]; exact Nat.le_max_right _ _
      refine ⟨kSeq j, hJk j hJkle, hJ j hJle⟩
    exact Filter.liminf_le_of_frequently_le' hfrequently
  have hxiCanonical := freeLimitRate_eq_torusRC_inverseCorrelationLength
    q μ hμ ξinv hRate
  have hW21' := hW21 q hh319
  change ((-TorusRC.inverseCorrelationLength q : ℝ) : EReal) ≤
    Filter.liminf outerRate8 Filter.atTop at hW21'
  have hW21'' : (-(ξinv : ℝ) : EReal) ≤ Filter.liminf outerRate8 Filter.atTop := by
    simpa [hxiCanonical] using hW21'
  have hxi : ξinv ≥ R := by
    by_contra hnot
    have hε : 0 < (R - ξinv) / 2 := by linarith
    have houter := houterBound ((R - ξinv) / 2) hε
    have hbetween : (-(ξinv : ℝ) : EReal) ≤ ((-R + (R - ξinv) / 2 : ℝ) : EReal) :=
      hW21''.trans houter
    have hreal : -ξinv ≤ -R + (R - ξinv) / 2 :=
      EReal.coe_le_coe_iff.mp hbetween
    linarith
  exact ⟨S, hS, by simpa [R] using hxi⟩

end PottsDiscontinuity.RCMProof
