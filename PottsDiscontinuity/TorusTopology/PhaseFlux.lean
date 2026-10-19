module

public import PottsDiscontinuity.Torus.DiamondIntersectionLocality
public import PottsDiscontinuity.Torus.DiamondSeamWinding

/-! Conserved seam flux splits equally among the modular phases. Each phase
of a chain winding b times has nonzero flux; this retains integer multiplicity. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus
open scoped Classical
variable {N M b : ℕ}
noncomputable section

/-- Signed chain flux across the horizontal seam from a specified vertex phase. -/
def phaseFlux (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (g : FaceVertex N M true → ZMod b) (k : ZMod b) (f : OpenDiamondEdge A → ℚ) : ℚ :=
  ∑ e with e.val.2.val=0 ∧ g (faceEndpoint hN hM true e.val false)=k, f e

/-- Conservation gives the same seam flux at adjacent phases. -/
theorem phaseFlux_successor_eq
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (g : FaceVertex N M true → ZMod b)
    (hg : ∀ e : OpenDiamondEdge A, diamondEdgeCluster hN hM A e=c →
      g (faceEndpoint hN hM true e.val true)-g (faceEndpoint hN hM true e.val false) =
        if e.val.2.val=0 then -1 else 0)
    (f : diamondCycleSpace hN hM A) (hs : SupportedOnDiamondCluster hN hM A c f)
    (k : ZMod b) : phaseFlux hN hM A g (k+1) f.val = phaseFlux hN hM A g k f.val := by
  let P : FaceVertex N M true → ℚ := fun u => if g u=k then 1 else 0
  have hp := diamondBoundary_pairing hN hM A P f.val
  rw [f.property] at hp
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hp
  have hterm (e : OpenDiamondEdge A) :
      diamondCoboundary hN hM A P e * f.val e =
        (if e.val.2.val=0 ∧ g (faceEndpoint hN hM true e.val false)=k+1 then f.val e else 0) -
        (if e.val.2.val=0 ∧ g (faceEndpoint hN hM true e.val false)=k then f.val e else 0) := by
    by_cases hc : diamondEdgeCluster hN hM A e=c
    · have he := hg e hc
      by_cases hy : e.val.2.val=0
      · simp only [hy,ite_true] at he
        have heq : g (faceEndpoint hN hM true e.val true)=k ↔
            g (faceEndpoint hN hM true e.val false)=k+1 := by
          constructor
          · intro h
            rw [h] at he
            linear_combination -he
          · intro h
            rw [h] at he
            linear_combination he
        simp only [diamondCoboundary_apply,P,heq,sub_mul,ite_mul,one_mul,zero_mul,hy,true_and]
      · simp only [hy,ite_false] at he
        have heq := sub_eq_zero.1 he
        simp [diamondCoboundary_apply,P,heq,hy]
    · rw [hs e hc]
      simp
  apply sub_eq_zero.1
  unfold phaseFlux
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← hterm]
  exact hp.symm

/-- There are b equal phase fluxes; a total winding b makes each equal -1. -/
theorem phaseFlux_eq_neg_one
    (hN : Even N) (hM : Even M) (A : RCConfig N M) (hb : 0 < b)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (g : FaceVertex N M true → ZMod b)
    (hg : ∀ e : OpenDiamondEdge A, diamondEdgeCluster hN hM A e=c →
      g (faceEndpoint hN hM true e.val true)-g (faceEndpoint hN hM true e.val false) =
        if e.val.2.val=0 then -1 else 0)
    (f : diamondCycleSpace hN hM A) (hs : SupportedOnDiamondCluster hN hM A c f)
    (hw : diamondWindingY A f.val = (b : ℚ)) (k : ZMod b) :
    phaseFlux hN hM A g k f.val = -1 := by
  let : NeZero b := ⟨hb.ne'⟩
  have hn (n : ℕ) : phaseFlux hN hM A g (n : ZMod b) f.val = phaseFlux hN hM A g 0 f.val := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ,phaseFlux_successor_eq hN hM A c g hg f hs,ih]
  have hall (t : ZMod b) : phaseFlux hN hM A g t f.val = phaseFlux hN hM A g 0 f.val := by
    rw [← ZMod.natCast_zmod_val t]
    exact hn t.val
  have htotal : (∑ t : ZMod b, phaseFlux hN hM A g t f.val) = -diamondWindingY A f.val := by
    unfold phaseFlux
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    calc
      _ = ∑ e : OpenDiamondEdge A, if e.val.2.val=0 then f.val e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases hy : e.val.2.val=0
        · simp only [hy,true_and]
          simp
        · simp [hy]
      _ = -diamondWindingY A f.val := by
        unfold diamondWindingY
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro e _
        by_cases hy : e.val.2.val=0 <;> simp [diamondSeamCrossY,hy]
  simp_rw [hall] at htotal
  rw [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,hw] at htotal
  have h0 : phaseFlux hN hM A g 0 f.val = -1 := by
    have hbq : (b : ℚ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hbq
    simpa only [mul_neg_one] using htotal
  rw [hall,h0]

end
end PottsDiscontinuity.TorusTopology
