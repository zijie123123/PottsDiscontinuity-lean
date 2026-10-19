module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Analytic
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Ordinary
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Pairing
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Phase

/-!
# Residue and cancellation for an ordinary T₁ pair

At an ordinary ML edge carrying the moved zero root on its L end, exactly one
word-coefficient edge factor has a pole. The fixed-amplitude pair cancels that
pole against the first-order scattering phase.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The coefficient product with one selected cyclic edge removed. -/
noncomputable def wordCoefficientEraseEdge {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin (n + 1)) : ℂ :=
  ∏ k ∈ (univ : Finset (Fin (n + 1))).erase a, wordEdgeFactor c p σ w k

/-- The pole residue of the amplitude-weighted ordinary word term. -/
theorem tendsto_t_mul_perturbedWordTerm {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.succ = l) (ha : w a.castSucc = false) (hb : w a.succ = true) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ *
        M c (z (p (σ a.castSucc))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc *
        wordPhase (N := N) x p σ w))) := by
  have hrot : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
  have hσa : σ a.castSucc ≠ l := by
    intro h
    exact Fin.castSucc_lt_succ.ne (σ.injective (h.trans hsig.symm))
  have hpne : p (σ a.castSucc) ≠ 0 := by
    intro h
    apply hσa
    exact hinj (h.trans hpl.symm)
  let m := M c (z (p (σ a.castSucc)))
  let q (t : ℝ) := perturbedMomenta p l t
  let edge (t : ℝ) := wordEdgeFactor c (q t) σ w a.castSucc
  let rest (t : ℝ) := ∏ k ∈ (univ : Finset (Fin (n + 1))).erase a.castSucc,
    wordEdgeFactor c (q t) σ w k
  have hlocal (t : ℝ) : edge t = m * L c (z t) - 1 := by
    dsimp [edge, q, m]
    have hroot : z (perturbedMomenta p l t (σ a.succ)) = z t := by
      rw [hsig, perturbedMomenta_at, hpl, zero_add]
    have hother : perturbedMomenta p l t (σ a.castSucc) = p (σ a.castSucc) :=
      perturbedMomenta_of_ne p l (σ a.castSucc) t hσa
    unfold wordEdgeFactor
    rw [hrot, ha, hb]
    simp only [Bool.false_eq_true, ↓reduceIte, hother, hroot]
  have hrest : ∀ t, rest t = rest 0 := by
    intro t
    dsimp only [rest]
    apply Finset.prod_congr rfl
    intro k hk
    have hka : k ≠ a.castSucc := (mem_erase.mp hk).1
    have hnext : finRotate (n + 1) k ≠ a.succ := by
      intro he
      apply hka
      exact (finRotate (n + 1)).injective (he.trans hrot.symm)
    have hσnext : σ (finRotate (n + 1) k) ≠ l := by
      intro h
      exact hnext (σ.injective (h.trans hsig.symm))
    have h3 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) t hσnext
    have h4 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) 0 hσnext
    unfold wordEdgeFactor
    cases hw : w k <;> cases hn : w (finRotate (n + 1) k)
    · have hkb : k ≠ a.succ := by
        intro he
        rw [he, hb] at hw
        contradiction
      have hσk : σ k ≠ l := by
        intro h
        exact hkb (σ.injective (h.trans hsig.symm))
      have h1 := perturbedMomenta_of_ne p l (σ k) t hσk
      have h2 := perturbedMomenta_of_ne p l (σ k) 0 hσk
      simp only [q, Bool.false_eq_true, ↓reduceIte]
      rw [h1, h2]
    · have hkb : k ≠ a.succ := by
        intro he
        rw [he, hb] at hw
        contradiction
      have hσk : σ k ≠ l := by
        intro h
        exact hkb (σ.injective (h.trans hsig.symm))
      have h1 := perturbedMomenta_of_ne p l (σ k) t hσk
      have h2 := perturbedMomenta_of_ne p l (σ k) 0 hσk
      simp only [q, Bool.false_eq_true, ↓reduceIte]
      rw [h1, h2, h3, h4]
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [q, ↓reduceIte]
      rw [h3, h4]
  have hprod (t : ℝ) : wordCoefficient c (q t) σ w = edge t * rest t := by
    change (∏ k, wordEdgeFactor c (q t) σ w k) = _
    simpa [edge, rest] using (Finset.mul_prod_erase (univ : Finset (Fin (n + 1)))
      (fun k => wordEdgeFactor c (q t) σ w k) (mem_univ a.castSucc)).symm
  have hlocalLimit : Tendsto (fun t : ℝ => (t : ℂ) * edge t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (m * (I * (c : ℂ)^2))) := by
    have htl := tendsto_t_mul_L_z_zero c
    have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      (continuous_ofReal.continuousAt : ContinuousAt (fun t : ℝ => (t : ℂ)) 0)
        |>.tendsto.mono_left nhdsWithin_le_nhds
    have heq : (fun t : ℝ => (t : ℂ) * edge t) =
        fun (t : ℝ) => m * ((t : ℂ) * L c (z t)) - (t : ℂ) := by
      funext t
      rw [hlocal]
      ring
    rw [heq]
    simpa using (tendsto_const_nhds.mul htl).sub ht
  have hphase : Continuous (fun t : ℝ =>
      wordPhase (N := N) x (q t) σ w) := by
    unfold wordPhase positionPhase q perturbedMomenta
    fun_prop
  have hfun : (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) =
      fun (t : ℝ) => amplitude (anisotropy c) p σ *
        ((t : ℂ) * edge t * rest 0) *
        wordPhase (N := N) x (q t) σ w := by
    funext t
    unfold perturbedWordTerm
    rw [hprod t, hrest t]
    dsimp [edge, q]
    ring
  have hrestT : Tendsto (fun _ : ℝ => rest 0) (𝓝[≠] (0 : ℝ)) (𝓝 (rest 0)) :=
    tendsto_const_nhds
  have hphaseT : Tendsto (fun t : ℝ => wordPhase (N := N) x (q t) σ w)
      (𝓝[≠] (0 : ℝ)) (𝓝 (wordPhase (N := N) x p σ w)) := by
    have h0 : q 0 = p := by
      funext k
      by_cases hk : k = l
      · subst k
        simp [q, perturbedMomenta]
      · simp [q, perturbedMomenta, hk]
    convert hphase.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    rw [h0]
  have hmul := (hlocalLimit.mul hrestT).mul hphaseT
  have hA : Tendsto (fun _ : ℝ => amplitude (anisotropy c) p σ)
      (𝓝[≠] (0 : ℝ)) (𝓝 (amplitude (anisotropy c) p σ)) := tendsto_const_nhds
  have hlim := hA.mul hmul
  have hfun' : (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) =
      fun (t : ℝ) => amplitude (anisotropy c) p σ *
        ((t : ℂ) * edge t * rest 0 *
          wordPhase (N := N) x (q t) σ w) := by
    calc
      _ = fun (t : ℝ) => amplitude (anisotropy c) p σ *
          ((t : ℂ) * edge t * rest 0) *
            wordPhase (N := N) x (q t) σ w := hfun
      _ = _ := by funext t; ring
  have hvalue : amplitude (anisotropy c) p σ *
      (m * (I * (c : ℂ)^2) * rest 0 *
        wordPhase (N := N) x p σ w) =
      I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ * m * rest 0 *
        wordPhase (N := N) x p σ w) := by ring
  rw [← hfun', hvalue] at hlim
  have hrest0 : rest 0 =
      wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc := by
    rfl
  rw [hrest0] at hlim
  simpa [m] using hlim

/-- The ordinary-edge paired terms have a finite limit, given by the phase slope
times the explicit pole residue. -/
theorem tendsto_ordinaryT1_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.succ = l) (ha : w a.castSucc = false) (hb : w a.succ = true) :
    Tendsto (fun t : ℝ =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap a.castSucc a.succ) w)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (((c : ℂ)^2 * amplitude (anisotropy c) p σ *
          M c (z (p (σ a.castSucc))) *
          wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc *
          wordPhase (N := N) x p σ w) *
        (zeroRootPhaseDerivative (N := N) (anisotropy c)
          (p (σ a.castSucc)) False : ℂ))) := by
  let f : ℝ → ℂ := fun t => Complex.exp (I *
    (zeroRootPhaseExponent (N := N) (anisotropy c)
      (p (σ a.castSucc)) False t : ℂ))
  let d : ℝ := zeroRootPhaseDerivative (N := N) (anisotropy c)
    (p (σ a.castSucc)) False
  let H := (c : ℂ)^2 * amplitude (anisotropy c) p σ *
    M c (z (p (σ a.castSucc))) *
    wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc *
    wordPhase (N := N) x p σ w
  have hterm := tendsto_t_mul_perturbedWordTerm (N := N) (c := c) x p hinj l hpl σ w a hsig ha hb
  have hterm' : Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w)
      (𝓝[≠] (0 : ℝ)) (𝓝 (I * H)) := by
    simpa [H] using hterm
  have hfd : HasDerivAt f (I * (d : ℂ)) 0 := by
    dsimp [f, d]
    exact hasDerivAt_zeroRootPhaseExp (N := N) (c := c)
      (p := p (σ a.castSucc)) hc False
  have hf0 : f 0 = 1 := by simp [f, zeroRootPhaseExponent]
  have hcancel := tendsto_pole_mul_one_sub_of_hasDerivAt hfd hf0 hterm'
  have heq : (fun t : ℝ =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap a.castSucc a.succ) w) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => perturbedWordTerm (N := N) c x p l t σ w * (1 - f t) := by
    filter_upwards [eventually_z_ne_one_zero] with t ht
    rw [perturbedWordTerm_adjacent_pair hc x p hp hinj l hpl t ht σ w a hsig ha hb]
    simp only [f, zeroRootPhaseExponent, ite_false, add_zero, Pi.sub_apply,
      Complex.ofReal_sub]
    ring
  have hpair := hcancel.congr' heq.symm
  simpa [H, d] using hpair

end PottsDiscontinuity.BetheAnsatz
