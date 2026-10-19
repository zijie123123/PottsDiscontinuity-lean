module

public import PottsDiscontinuity.Torus.CorrectedRCWeight
public import PottsDiscontinuity.Torus.LoopRotationNumber
public import PottsDiscontinuity.Torus.OrientationEquiv
public import PottsDiscontinuity.Torus.Parameters
public import PottsDiscontinuity.TorusLoops.WindingClusterCount

/-!
# Turning weights of oriented loop configurations

The source weight is the exponential of the sum of oriented loop turns. The two
homological turning classifications are explicit premises here; they are proved in
`TorusTopology/ZeroWindingTurning.lean` and `TorusTopology/NonzeroWindingTurning.lean`
and discharged in `Torus/Corollary313Final.lean`. No theorem in this file claims them.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
open PottsDiscontinuity.TorusLoops
open Classical

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The turning classification for zero homological winding, stated on the torus loop carrier
`Loop hN hM (rcSmoothing A)`: every such loop has rotation number `±1`. It is proved by
`TorusTopology.loopRotationNumber_eq_pm_one_of_zero_winding`. -/
def ZeroWindingTurnPremise (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (A : RCConfig N M) : Prop :=
  ∀ q : Loop hN hM (rcSmoothing A),
    loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) j q = 0 →
    loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) (horizontalCross i) q = 0 →
    loopRotationNumber (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) q = 1 ∨
      loopRotationNumber (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) q = -1

/-- The turning classification for nonzero homological winding, stated on the torus loop
carrier `Loop hN hM (rcSmoothing A)`: every such loop has rotation number `0`. It is proved by
`TorusTopology.loopRotationNumber_eq_zero_of_nonzero_winding`. -/
def NonzeroWindingTurnPremise (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (A : RCConfig N M) : Prop :=
  ∀ q : Loop hN hM (rcSmoothing A),
    (loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 ∨
      loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) (horizontalCross i) q ≠ 0) →
    loopRotationNumber (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) q = 0

/-- Product of the exponential full-turn weights of all oriented loops. -/
noncomputable def orientedLoopWeight (lam : ℝ) (ω : ArrowConfig N M)
    (s : Smoothing N M) (h : CompatibleConfig ω s) : ℝ :=
  ∏ q : DirectedLoop ω s h, Real.exp (lam * (loopRotationNumber ω s h q : ℤ))

/-- Loop-factor product for an explicit Boolean choice of each canonical loop direction. -/
noncomputable def chosenLoopWeight (lam : ℝ) (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (F : Loop hN hM (rcSmoothing A) → Bool) : ℝ :=
  ∏ q : Loop hN hM (rcSmoothing A),
    Real.exp (lam * (if F q then
      loopRotationNumber (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) q else
      -loopRotationNumber (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) q : ℤ))

/-- The exponential loop weight agrees with the local turn product. -/
theorem orientedLoopWeight_eq_smoothingWeight (lam : ℝ) (ω : ArrowConfig N M)
    (s : Smoothing N M) (h : CompatibleConfig ω s) :
    orientedLoopWeight lam ω s h = smoothingWeight lam ω s := by
  unfold orientedLoopWeight
  rw [← Real.exp_sum]
  have hsum :
      (∑ q : DirectedLoop ω s h,
        lam * (loopRotationNumber ω s h q : ℤ)) =
      lam / 4 * (∑ q : DirectedLoop ω s h, (loopTurn ω s h q : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [loopTurn_eq_four_mul_rotationNumber]
    push_cast
    ring
  rw [hsum]
  have hturn :
      (∑ q : DirectedLoop ω s h, (loopTurn ω s h q : ℤ) : ℝ) =
        (totalQuarterTurn ω s : ℝ) := by
    exact_mod_cast (sum_loopTurn ω s h)
  rw [hturn]
  exact (smoothingWeight_eq_exp h lam).symm

/-- Reorientation identifies the cyclic-loop weight with the Boolean loop-factor product. -/
theorem orientedLoopWeight_eq_chosenLoopWeight (lam : ℝ) (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (ω : ArrowConfig N M)
    (h : CompatibleConfig ω (rcSmoothing A)) :
    orientedLoopWeight lam ω (rcSmoothing A) h =
      chosenLoopWeight lam hN hM A
        (loopOrientation (checkerArrows N M) (rcSmoothing A)
          (checkerArrows_compatible hN hM (rcSmoothing A)) ω h) := by
  classical
  let e := loopReorientEquiv (checkerArrows N M) ω (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) h
  unfold orientedLoopWeight chosenLoopWeight
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro q _
  rw [loopRotationNumber_reorient]

/-- Summing the oriented loop weights gives one factor `2` per winding loop and
one factor `sqrt q` per zero-winding loop. The two global turn classifications are
explicit premises in the theorem signature. -/
theorem sum_chosenLoopWeight_eq_loopFactors (lam qval : ℝ)
    (hLam : Real.exp lam + Real.exp (-lam) = Real.sqrt qval)
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (hzero : ZeroWindingTurnPremise hN hM i j A)
    (hnonzero : NonzeroWindingTurnPremise hN hM i j A) :
    (∑ F : Loop hN hM (rcSmoothing A) → Bool,
      chosenLoopWeight lam hN hM A F) =
      (2 : ℝ) ^ windingLoopCount hN hM i j A *
        Real.sqrt qval ^ (rcLoopCount hN hM A - windingLoopCount hN hM i j A) := by
  classical
  let W := windingLoopSet hN hM i j A
  let rot (q : Loop hN hM (rcSmoothing A)) :=
    loopRotationNumber (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) q
  have hp :
      (∑ F : Loop hN hM (rcSmoothing A) → Bool,
        ∏ q : Loop hN hM (rcSmoothing A),
          Real.exp (lam * (if F q then rot q else -rot q : ℤ))) =
      ∏ q : Loop hN hM (rcSmoothing A),
        ∑ b : Bool, Real.exp (lam * (if b then rot q else -rot q : ℤ)) := by
    simpa only [Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
        (fun q : Loop hN hM (rcSmoothing A) => fun b =>
          Real.exp (lam * (if b then rot q else -rot q : ℤ))))
  have hlocal (q : Loop hN hM (rcSmoothing A)) :
      (∑ b : Bool, Real.exp (lam * (if b then rot q else -rot q : ℤ))) =
        if q ∈ W then 2 else Real.sqrt qval := by
    by_cases hW : q ∈ W
    · have hwind :
          loopVertical (checkerArrows N M) (rcSmoothing A)
              (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 ∨
            loopSum (checkerArrows N M) (rcSmoothing A)
              (checkerArrows_compatible hN hM (rcSmoothing A)) (horizontalCross i) q ≠ 0 := by
        simpa [W, windingLoopSet] using hW
      have hr := hnonzero q hwind
      change rot q = 0 at hr
      rw [ite_eq_left hW]
      simp [hr]
    · have hnotwind :
          ¬ (loopVertical (checkerArrows N M) (rcSmoothing A)
                (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 ∨
              loopSum (checkerArrows N M) (rcSmoothing A)
                (checkerArrows_compatible hN hM (rcSmoothing A)) (horizontalCross i) q ≠ 0) := by
        simpa [W, windingLoopSet] using hW
      have hv : loopVertical (checkerArrows N M) (rcSmoothing A)
          (checkerArrows_compatible hN hM (rcSmoothing A)) j q = 0 := by
        by_contra h
        exact hnotwind (Or.inl h)
      have hh : loopSum (checkerArrows N M) (rcSmoothing A)
          (checkerArrows_compatible hN hM (rcSmoothing A)) (horizontalCross i) q = 0 := by
        by_contra h
        exact hnotwind (Or.inr h)
      rcases hzero q hv hh with hr | hr
      · change rot q = 1 at hr
        rw [ite_eq_right hW]
        simp [hr, hLam]
      · change rot q = -1 at hr
        rw [ite_eq_right hW]
        simp [hr, hLam, add_comm]
  unfold chosenLoopWeight
  rw [hp]
  simp_rw [hlocal]
  have hsplit :
      (Finset.univ.filter fun q : Loop hN hM (rcSmoothing A) => q ∈ W).card +
          (Finset.univ.filter fun q : Loop hN hM (rcSmoothing A) => q ∉ W).card =
        Fintype.card (Loop hN hM (rcSmoothing A)) := by
    have hs := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Loop hN hM (rcSmoothing A)))) (fun q => q ∈ W)
    simpa using hs
  have hfilter :
      Finset.univ.filter (fun q : Loop hN hM (rcSmoothing A) => q ∈ W) = W := by
    ext q
    simp [W]
  have hcardcomp :
      (Finset.univ.filter fun q : Loop hN hM (rcSmoothing A) => q ∉ W).card =
        Fintype.card (Loop hN hM (rcSmoothing A)) - W.card := by
    have hs := hsplit
    rw [hfilter] at hs
    omega
  rw [Finset.prod_ite]
  rw [hfilter]
  simp only [Finset.prod_const]
  rw [hcardcomp]
  simp [W, windingLoopCount, rcLoopCount, loopCount]

/-- The compatible arrow fields are exactly the Boolean loop orientations, so their
oriented weight sum is the same product of loop factors. -/
theorem sum_compatibleOrientedLoopWeight_eq_loopFactors (lam qval : ℝ)
    (hLam : Real.exp lam + Real.exp (-lam) = Real.sqrt qval)
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (hzero : ZeroWindingTurnPremise hN hM i j A)
    (hnonzero : NonzeroWindingTurnPremise hN hM i j A) :
    (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
      orientedLoopWeight lam x.val (rcSmoothing A) x.property) =
      (2 : ℝ) ^ windingLoopCount hN hM i j A *
        Real.sqrt qval ^ (rcLoopCount hN hM A - windingLoopCount hN hM i j A) := by
  classical
  let e := orientationEquiv (checkerArrows N M) (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A))
  calc
    _ = ∑ F : Loop hN hM (rcSmoothing A) → Bool, chosenLoopWeight lam hN hM A F := by
      refine Fintype.sum_equiv e _ _ ?_
      intro x
      exact orientedLoopWeight_eq_chosenLoopWeight lam hN hM A x.val x.property
    _ = _ := sum_chosenLoopWeight_eq_loopFactors lam qval hLam hN hM i j A hzero hnonzero

/-- A failed compatibility condition forces a zero local product because one vertex
has no allowed smoothing. -/
theorem smoothingWeight_eq_zero_of_not_compatible (lam : ℝ) (ω : ArrowConfig N M)
    (s : Smoothing N M) (h : ¬ CompatibleConfig ω s) : smoothingWeight lam ω s = 0 := by
  classical
  obtain ⟨v, hv⟩ := not_forall.mp h
  unfold smoothingWeight
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  simp [turnWeight, hv]

/-- A smoothing contributes the sum of its compatible oriented-loop weights to the
six-vertex smoothing expansion. Incompatible arrow/smoothing pairs have zero local weight. -/
theorem sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight (lam : ℝ)
    (s : Smoothing N M) :
    (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s},
      orientedLoopWeight lam x.val s x.property) =
      ∑ ω : ArrowConfig N M, smoothingWeight lam ω s := by
  classical
  have hsub :
      (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s}, smoothingWeight lam x.val s) =
        ∑ ω : ArrowConfig N M, smoothingWeight lam ω s := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun ω : ArrowConfig N M => CompatibleConfig ω s)
      (by intro ω; simp) (fun ω => smoothingWeight lam ω s)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hc : CompatibleConfig ω s
    · simp [hc]
    · simp [hc, smoothingWeight_eq_zero_of_not_compatible lam ω s hc]
  calc
    _ = ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s}, smoothingWeight lam x.val s := by
      apply Fintype.sum_congr
      intro x
      exact orientedLoopWeight_eq_smoothingWeight lam x.val s x.property
    _ = _ := hsub

/-- Lemma 3.10 in the corrected-weight form: the corrected RC weight is the
normalization times the sum of all compatible oriented-loop weights. -/
theorem torusCorrectedRCWeight_eq_normalization_mul_orientedSum
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (A : RCConfig N M)
    (hzero : ZeroWindingTurnPremise hN hM i j A)
    (hnonzero : NonzeroWindingTurnPremise hN hM i j A) :
    torusCorrectedRCWeight hN hM i j q A =
      torusNormalization q N M *
        (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
          orientedLoopWeight (Real.arcosh (Real.sqrt q.val / 2)) x.val
            (rcSmoothing A) x.property) := by
  have hLam := exp_add_exp_neg_arcosh q.val hq
  calc
    torusCorrectedRCWeight hN hM i j q A =
        torusNormalization q N M *
          (2 : ℝ) ^ windingLoopCount hN hM i j A *
            Real.sqrt q.val ^ (rcLoopCount hN hM A - windingLoopCount hN hM i j A) :=
      torusCorrectedRCWeight_eq_loopFactors hN hM i j q A
    _ = _ := by
      rw [sum_compatibleOrientedLoopWeight_eq_loopFactors
        (Real.arcosh (Real.sqrt q.val / 2)) q.val hLam hN hM i j A hzero hnonzero]
      ring

/-- Corollary 3.13(i), conditional only on the two homological turning classifications;
the unconditional form is `corollary_313_i_final` in `Torus/Corollary313Final.lean`. -/
theorem corollary_313_i
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (i : Fin N) (j : Fin M)
    (hturn : ∀ A : RCConfig N M,
      ZeroWindingTurnPremise hN hM i j A ∧ NonzeroWindingTurnPremise hN hM i j A) :
    (∑ A : RCConfig N M, torusCorrectedRCWeight hN hM i j q A) =
      torusNormalization q N M *
        Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M := by
  classical
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  have hLam := exp_add_exp_neg_arcosh q.val hq
  calc
    _ = ∑ A : RCConfig N M,
          torusNormalization q N M *
            (∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
              orientedLoopWeight lam x.val (rcSmoothing A) x.property) := by
      apply Finset.sum_congr rfl
      intro A _
      exact torusCorrectedRCWeight_eq_normalization_mul_orientedSum hN hM i j q hq A
        (hturn A).1 (hturn A).2
    _ = torusNormalization q N M *
          ∑ A : RCConfig N M,
            ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω (rcSmoothing A)},
              orientedLoopWeight lam x.val (rcSmoothing A) x.property := by
      rw [Finset.mul_sum]
    _ = torusNormalization q N M *
          ∑ s : Smoothing N M,
            ∑ x : {ω : ArrowConfig N M // CompatibleConfig ω s},
              orientedLoopWeight lam x.val s x.property := by
      refine congrArg (fun x : ℝ => torusNormalization q N M * x) ?_
      exact Fintype.sum_equiv (rcSmoothingEquiv N M) _ _ (by intro A; rfl)
    _ = torusNormalization q N M *
          ∑ s : Smoothing N M, ∑ ω : ArrowConfig N M, smoothingWeight lam ω s := by
      apply congrArg (fun x : ℝ => torusNormalization q N M * x)
      exact Finset.sum_congr rfl
        (fun s _ => sum_compatibleOrientedLoopWeight_eq_sum_smoothingWeight lam s)
    _ = torusNormalization q N M *
          ∑ ω : ArrowConfig N M, ∑ s : Smoothing N M, smoothingWeight lam ω s := by
      refine congrArg (fun x : ℝ => torusNormalization q N M * x) ?_
      rw [Finset.sum_comm]
    _ = torusNormalization q N M *
          Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M := by
      rw [sum_smoothingWeight_eq_Z6V_sqrt q.val hq]

end PottsDiscontinuity.Torus
