module

public import PottsDiscontinuity.TorusLoops.LoopTailUnionBound

/-!
# Finite-energy winding-loop tail after the root-set union bound

Combining the seam-closing estimate with the root-set exploration estimate
gives an explicit probability bound for a large homological loop count.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC

variable {N M : ℕ}

noncomputable section

/-- The two deleted seams contain at most `N + M` indexed edges. -/
theorem rectangleSeamIndices_card_le_add
    (hNp : 0 < N) (hMp : 0 < M) :
    (rectangleSeamIndices (N := N) (M := M)).card ≤ N + M := by
  classical
  let : NeZero N := ⟨Nat.ne_of_gt hNp⟩
  let : NeZero M := ⟨Nat.ne_of_gt hMp⟩
  let sx : Finset (Fin N × Fin M) :=
    Finset.univ.filter fun v => v.1.val = 0
  let sy : Finset (Fin N × Fin M) :=
    Finset.univ.filter fun v => v.2.val = 0
  have hsplit : rectangleSeamIndices (N := N) (M := M) = sx ∪ sy := by
    ext v
    simp [rectangleSeamIndices, sx, sy]
  have hsx : sx = Finset.univ.image (fun j : Fin M => (0, j)) := by
    ext v
    simp only [sx, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_univ]
    constructor
    · intro hv
      refine ⟨v.2, ?_⟩
      exact Prod.ext (Fin.ext hv.symm) rfl
    · rintro ⟨j, h⟩
      have hv := congrArg (fun z : Fin N × Fin M => z.1.val) h
      simpa using hv.symm
  have hsy : sy = Finset.univ.image (fun i : Fin N => (i, 0)) := by
    ext v
    simp only [sy, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_univ]
    constructor
    · intro hv
      refine ⟨v.1, ?_⟩
      exact Prod.ext rfl (Fin.ext hv.symm)
    · rintro ⟨i, h⟩
      have hv := congrArg (fun z : Fin N × Fin M => z.2.val) h
      simpa using hv.symm
  have hsx_card : sx.card = M := by
    rw [hsx, Finset.card_image_of_injective _ (by
      intro a b h
      exact congrArg Prod.snd h)]
    simp
  have hsy_card : sy.card = N := by
    rw [hsy, Finset.card_image_of_injective _ (by
      intro a b h
      exact congrArg Prod.fst h)]
    simp
  rw [hsplit]
  calc
    (sx ∪ sy).card ≤ sx.card + sy.card := Finset.card_union_le _ _
    _ = M + N := by rw [hsx_card, hsy_card]
    _ = N + M := Nat.add_comm _ _

/-- Corrected (3.17) followed by the exploration union bound, before division
by the finite-energy cost of closing all seams. -/
theorem torusRCProbability_windingTail_mul_seam_le_rootUnion
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) :
    (1 - (rcCriticalParameter q).val) ^
        (rectangleSeamIndices (N := N) (M := M)).card *
        phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
      (2 : ℝ) ^ M * rectangleFreeOneArmProbability q (N / 2 - 1) ^
        ((m - 3 * N + 1) / 2) := by
  calc
    (1 - (rcCriticalParameter q).val) ^
        (rectangleSeamIndices (N := N) (M := M)).card *
        phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
      rectangleFKEventProbability hN hM q
        (rectangleFKCrossingEvent hN hM ((m - 3 * N + 1) / 2)) :=
      torusRCProbability_windingTail_le_rectangleFKCrossings
        hN hM hNp hMp q m
    _ ≤ (2 : ℝ) ^ M * rectangleFreeOneArmProbability q (N / 2 - 1) ^
        ((m - 3 * N + 1) / 2) :=
      rectangleFKCrossingEvent_probability_le_rootUnion hN hM q _

/-- The winding-loop tail bound with its finite-energy cost divided out and
with the seam count replaced by the linear estimate `N + M`. -/
theorem torusRCProbability_windingTail_le_rootUnion
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) :
    phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
      ((2 : ℝ) ^ M * rectangleFreeOneArmProbability q (N / 2 - 1) ^
        ((m - 3 * N + 1) / 2)) /
        (1 - (rcCriticalParameter q).val) ^ (N + M) := by
  have hα : 0 < 1 - (rcCriticalParameter q).val := by
    exact sub_pos.mpr (criticalParameter_lt_one q)
  have hαle : 1 - (rcCriticalParameter q).val ≤ 1 := by
    linarith [criticalParameter_pos q]
  have hcard := rectangleSeamIndices_card_le_add hNp hMp
  have hpow :
      (1 - (rcCriticalParameter q).val) ^ (N + M) ≤
        (1 - (rcCriticalParameter q).val) ^
          (rectangleSeamIndices (N := N) (M := M)).card :=
    pow_le_pow_of_le_one hα.le hαle hcard
  have hmul := torusRCProbability_windingTail_mul_seam_le_rootUnion
    hN hM hNp hMp q m
  have hprob :
      phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
        ((2 : ℝ) ^ M * rectangleFreeOneArmProbability q (N / 2 - 1) ^
          ((m - 3 * N + 1) / 2)) /
          (1 - (rcCriticalParameter q).val) ^
            (rectangleSeamIndices (N := N) (M := M)).card := by
    apply (le_div_iff₀ (pow_pos hα _)).2
    simpa [mul_comm] using hmul
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    unfold rectangleFreeOneArmProbability
    exact NNReal.coe_nonneg _
  have hnum : 0 ≤ (2 : ℝ) ^ M * rectangleFreeOneArmProbability q
      (N / 2 - 1) ^ ((m - 3 * N + 1) / 2) :=
    mul_nonneg (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)
      (pow_nonneg hρ _)
  exact hprob.trans (div_le_div_of_nonneg_left hnum (pow_pos hα _ ) hpow)

end

end PottsDiscontinuity.TorusLoops
