module

public import PottsDiscontinuity.Torus.NetEuler
public import PottsDiscontinuity.TorusLoops.FiniteEnergy

/-!
# The torus random-cluster loop weight identity

The proved Euler/net relation converts the critical RC weight into the loop weight
of Lemma 3.9, with the exact real-power normalization from the paper.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The exact factor C = q^(NM/4) (1 + sqrt q)^(-NM). -/
noncomputable def torusNormalization (q : Set.Ici (1 : ℝ)) (N M : ℕ) : ℝ :=
  q.val ^ ((N * M : ℝ) / 4) * (1 + Real.sqrt q.val) ^ (-(N * M : ℝ))

theorem torusNormalization_pos (q : Set.Ici (1 : ℝ)) (N M : ℕ) :
    0 < torusNormalization q N M := by
  unfold torusNormalization
  apply mul_pos <;> apply Real.rpow_pos_of_pos
  · have hq : (1 : ℝ) ≤ q.val := q.property
    linarith
  · positivity

theorem torusNormalization_eq_sqrt_pow (hN : Even N) (q : Set.Ici (1 : ℝ)) :
    torusNormalization q N M =
      Real.sqrt q.val ^ (N * M / 2) / (1 + Real.sqrt q.val) ^ (N * M) := by
  have hq : 0 ≤ q.val := le_trans (by norm_num) q.property
  have ht : 2 * (N * M / 2) = N * M := Nat.mul_div_cancel' (hN.mul_right M).two_dvd
  have hv : ((N * M / 2 : ℕ) : ℝ) = (N * M : ℝ) / 2 := by
    have he : (2 : ℝ) * (N * M / 2 : ℕ) = (N * M : ℝ) := by exact_mod_cast ht
    linarith
  have hs : Real.sqrt q.val ^ (N * M / 2) = q.val ^ ((N * M : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq]
    congr 1
    rw [hv]
    ring
  rw [torusNormalization, ← hs, Real.rpow_neg (by positivity), ← Nat.cast_mul, Real.rpow_natCast]
  rfl

/-- Lemma 3.9 on the actual indexed torus graph and the winding-defined net indicator. -/
theorem torusRCWeight_eq_loopWeight (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M) :
    torusRCWeight hN hM q A = torusNormalization q N M *
      Real.sqrt q.val ^ (rcLoopCount hN hM A + 2 * rcNetIndicator hN hM A) := by
  let t := Real.sqrt q.val
  let d := 1 + t
  have hd : d ≠ 0 := by dsimp [d, t]; positivity
  have hq : 0 ≤ q.val := le_trans (by norm_num) q.property
  have hp : (rcCriticalParameter q).val = t / d := rfl
  have hc : 1 - (rcCriticalParameter q).val = 1 / d := by
    rw [hp]
    field_simp [hd]
    dsimp [d]
    ring
  have hk : q.val ^ clusterCount hN hM true A = t ^ (2 * clusterCount hN hM true A) := by
    calc
      _ = (t ^ 2) ^ clusterCount hN hM true A :=
        congrArg (fun x : ℝ => x ^ clusterCount hN hM true A) (Real.sq_sqrt hq).symm
      _ = _ := (pow_mul _ _ _).symm
  have he := euler_netIndicator hN hM A
  have hn : openCount A + 2 * clusterCount hN hM true A =
      N * M / 2 + (rcLoopCount hN hM A + 2 * rcNetIndicator hN hM A) := by omega
  calc
    torusRCWeight hN hM q A =
        (t ^ openCount A * t ^ (2 * clusterCount hN hM true A)) /
          (d ^ openCount A * d ^ closedCount A) := by
      rw [torusRCWeight, hc, hp, hk, div_pow, div_pow, one_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = t ^ (openCount A + 2 * clusterCount hN hM true A) /
        d ^ (openCount A + closedCount A) := by rw [pow_add, pow_add]
    _ = (t ^ (N * M / 2) / d ^ (N * M)) *
        t ^ (rcLoopCount hN hM A + 2 * rcNetIndicator hN hM A) := by
      rw [hn, openCount_add_closedCount, pow_add]
      ring
    _ = _ := by rw [torusNormalization_eq_sqrt_pow hN]

end PottsDiscontinuity.Torus
