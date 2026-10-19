module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Residue
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPair

/-!
# The seam residue and paired limit

At a seam ML edge the unique pole is the cyclic edge from the last slot to
slot zero. Its residue combines with the corrected phase slope containing `N`.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The amplitude-weighted seam word term has an explicit pole residue. -/
theorem tendsto_t_mul_perturbedWordTerm_seam {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hsig : σ 0 = l) (hLast : w (Fin.last n) = false) (hZero : w 0 = true) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ *
        M c (z (p (σ (Fin.last n)))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w (Fin.last n) *
        wordPhase (N := N) x p σ w))) := by
  let u := Fin.last n
  have hu0 : u ≠ (0 : Fin (n + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp [u] at hv
    omega
  have hrot : finRotate (n + 1) u = 0 := by simp [u]
  have hσu : σ u ≠ l := by
    intro h
    exact hu0 (σ.injective (h.trans hsig.symm))
  have hpσu : p (σ u) ≠ 0 := by
    intro h
    apply hσu
    exact hinj (h.trans hpl.symm)
  let m := M c (z (p (σ u)))
  let q (t : ℝ) := perturbedMomenta p l t
  let edge (t : ℝ) := wordEdgeFactor c (q t) σ w u
  let rest (t : ℝ) := ∏ k ∈ (univ : Finset (Fin (n + 1))).erase u,
    wordEdgeFactor c (q t) σ w k
  have hlocal (t : ℝ) : edge t = m * L c (z t) - 1 := by
    dsimp [edge, q, m]
    have hroot : z (perturbedMomenta p l t (σ 0)) = z t := by
      rw [hsig, perturbedMomenta_at, hpl, zero_add]
    have hother : perturbedMomenta p l t (σ u) = p (σ u) :=
      perturbedMomenta_of_ne p l (σ u) t hσu
    unfold wordEdgeFactor
    rw [hrot, hLast, hZero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hother, hroot]
  have hrest : ∀ t, rest t = rest 0 := by
    intro t
    dsimp only [rest]
    apply Finset.prod_congr rfl
    intro k hk
    have hku : k ≠ u := (mem_erase.mp hk).1
    have hnext : finRotate (n + 1) k ≠ 0 := by
      intro he
      apply hku
      exact (finRotate (n + 1)).injective (he.trans hrot.symm)
    have hσnext : σ (finRotate (n + 1) k) ≠ l := by
      intro h
      exact hnext (σ.injective (h.trans hsig.symm))
    have h3 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) t hσnext
    have h4 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) 0 hσnext
    cases hw : w k <;> cases hnxt : w (finRotate (n + 1) k)
    · have hσk : σ k ≠ l := by
        intro h
        have hk0 : k = 0 := σ.injective (h.trans hsig.symm)
        subst k
        rw [hZero] at hw
        contradiction
      have h1 := perturbedMomenta_of_ne p l (σ k) t hσk
      have h2 := perturbedMomenta_of_ne p l (σ k) 0 hσk
      unfold wordEdgeFactor
      simp only [q, hw, hnxt, Bool.false_eq_true, ↓reduceIte]
      rw [h1, h2]
    · have hσk : σ k ≠ l := by
        intro h
        have hk0 : k = 0 := σ.injective (h.trans hsig.symm)
        subst k
        rw [hZero] at hw
        contradiction
      have h1 := perturbedMomenta_of_ne p l (σ k) t hσk
      have h2 := perturbedMomenta_of_ne p l (σ k) 0 hσk
      unfold wordEdgeFactor
      simp only [q, hw, hnxt, Bool.false_eq_true, ↓reduceIte]
      rw [h1, h2, h3, h4]
    · unfold wordEdgeFactor
      simp only [hw, hnxt, Bool.false_eq_true, ↓reduceIte]
    · unfold wordEdgeFactor
      simp only [q, hw, hnxt, ↓reduceIte]
      rw [h3, h4]
  have hprod (t : ℝ) : wordCoefficient c (q t) σ w = edge t * rest t := by
    change (∏ k, wordEdgeFactor c (q t) σ w k) = _
    simpa [edge, rest] using (Finset.mul_prod_erase (univ : Finset (Fin (n + 1)))
      (fun k => wordEdgeFactor c (q t) σ w k) (mem_univ u)).symm
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
  have hphase : Continuous (fun t : ℝ => wordPhase (N := N) x (q t) σ w) := by
    unfold wordPhase positionPhase q perturbedMomenta
    fun_prop
  have hfun : (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) =
      fun (t : ℝ) => amplitude (anisotropy c) p σ *
        ((t : ℂ) * edge t * rest 0) * wordPhase (N := N) x (q t) σ w := by
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
        ((t : ℂ) * edge t * rest 0 * wordPhase (N := N) x (q t) σ w) := by
    calc
      _ = fun (t : ℝ) => amplitude (anisotropy c) p σ *
          ((t : ℂ) * edge t * rest 0) * wordPhase (N := N) x (q t) σ w := hfun
      _ = _ := by funext t; ring
  have hvalue : amplitude (anisotropy c) p σ *
      (m * (I * (c : ℂ)^2) * rest 0 * wordPhase (N := N) x p σ w) =
      I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ * m * rest 0 *
        wordPhase (N := N) x p σ w) := by ring
  rw [← hfun', hvalue] at hlim
  have hrest0 : rest 0 =
      wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w u := by rfl
  rw [hrest0] at hlim
  simpa [m, u] using hlim

/-- The seam-paired terms have a finite limit with the corrected phase slope,
including the additional `N` contribution. -/
theorem tendsto_seamT1_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hsig : σ 0 = l) (hLast : w (Fin.last n) = false) (hZero : w 0 = true) :
    Tendsto (fun t : ℝ =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap (Fin.last n) 0) w)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (((c : ℂ)^2 * amplitude (anisotropy c) p σ *
          M c (z (p (σ (Fin.last n)))) *
          wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w (Fin.last n) *
          wordPhase (N := N) x p σ w) *
        (zeroRootPhaseDerivative (N := N) (anisotropy c)
          (p (σ (Fin.last n))) True : ℂ))) := by
  let f : ℝ → ℂ := fun t => Complex.exp (I *
    (zeroRootPhaseExponent (N := N) (anisotropy c)
      (p (σ (Fin.last n))) True t : ℂ))
  let d : ℝ := zeroRootPhaseDerivative (N := N) (anisotropy c)
    (p (σ (Fin.last n))) True
  let H := (c : ℂ)^2 * amplitude (anisotropy c) p σ *
    M c (z (p (σ (Fin.last n)))) *
    wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w (Fin.last n) *
    wordPhase (N := N) x p σ w
  have hterm := tendsto_t_mul_perturbedWordTerm_seam (N := N) (c := c) x p hinj
    l hpl σ w hn hsig hLast hZero
  have hterm' : Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w)
      (𝓝[≠] (0 : ℝ)) (𝓝 (I * H)) := by
    simpa [H] using hterm
  have hfd : HasDerivAt f (I * (d : ℂ)) 0 := by
    dsimp [f, d]
    exact hasDerivAt_zeroRootPhaseExp (N := N) (c := c)
      (p := p (σ (Fin.last n))) hc True
  have hf0 : f 0 = 1 := by simp [f, zeroRootPhaseExponent]
  have hcancel := tendsto_pole_mul_one_sub_of_hasDerivAt hfd hf0 hterm'
  have heq : (fun t : ℝ =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap (Fin.last n) 0) w) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => perturbedWordTerm (N := N) c x p l t σ w * (1 - f t) := by
    filter_upwards [eventually_z_ne_one_zero] with t ht
    rw [perturbedWordTerm_seam_pair hc x p hp hinj l hpl hBE t ht σ w
      hn hsig hLast hZero]
    simp only [f, zeroRootPhaseExponent, ite_true, Pi.sub_apply, Pi.add_apply,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    ring
  have hpair := hcancel.congr' heq.symm
  simpa [H, d] using hpair

end PottsDiscontinuity.BetheAnsatz
