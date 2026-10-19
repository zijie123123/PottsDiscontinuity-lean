module

public import PottsDiscontinuity.TorusTopology.IntegralBoundary
public import PottsDiscontinuity.TorusTopology.SeamWinding

/-! Integer boundary decompositions within a specified original primal cluster.
This retains winding multiplicity; a vertically winding loop need not wind
only once around the torus. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
open scoped Classical
variable {N M : ℕ}
noncomputable section

/-- Integer boundary labels on the medial-loop quotient. -/
def loopBoundaryIntLabel (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (F : RibbonBoundaryComponent hN hM A → ℤ) : Loop hN hM (rcSmoothing A) → ℤ :=
  Quotient.lift (fun d => F (ribbonBoundaryOf hN hM A d)) (fun _ _ h => by
    apply congrArg F
    apply Quotient.sound
    rwa [ribbonBoundary_eq_directedStep])

/-- Integer decomposition into boundary loops of the same actual primal
cluster. The integer coefficients are obtained by flooring a face potential. -/
theorem exists_integral_loop_expansion_supported
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (f : diamondCycleSpace hN hM A) (hf : f ∈ ribbonBoundarySpace hN hM A)
    (hs : SupportedOnDiamondCluster hN hM A c f)
    (hint : ∀ e : OpenDiamondEdge A, ∃ z : ℤ, f.val e = z) :
    ∃ a : Loop hN hM (rcSmoothing A) → ℤ,
      f.val = ∑ q with loopPrimalCluster hN hM A q = c,
        (a q : ℚ) • (loopBoundaryCycle hN hM A q).val := by
  classical
  obtain ⟨F,hF⟩ := exists_int_face_potential_of_integral_boundary hN hM A f hf hint
  refine ⟨loopBoundaryIntLabel hN hM A F,?_⟩
  funext e
  have he := congrFun hF e
  change (F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,true))) : ℚ) -
    (F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,false))) : ℚ) = f.val e at he
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,loopBoundaryCycle,
    ribbonFaceBoundary,LinearMap.coe_mk,AddHom.coe_mk,loopBoundaryFunction_corner,
    mul_sub,mul_ite,mul_one,mul_zero,Finset.sum_sub_distrib,
    Finset.sum_ite_eq,Finset.mem_filter,Finset.mem_univ,true_and,loopPrimalCluster_end]
  by_cases hc : diamondEdgeCluster hN hM A e = c
  · simpa only [hc,ite_true,loopBoundaryIntLabel,directedLoopOf,Quotient.lift_mk] using he.symm
  · simp only [hc,ite_false,sub_self]
    exact hs e hc

/-- The integer loop expansion also preserves the exact seam intersection. -/
theorem windingY_eq_sum_of_loop_expansion
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (j : Fin M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (f : diamondCycleSpace hN hM A) (a : Loop hN hM (rcSmoothing A) → ℤ)
    (ha : f.val = ∑ q with loopPrimalCluster hN hM A q = c,
      (a q : ℚ) • (loopBoundaryCycle hN hM A q).val) :
    diamondWindingY A f.val =
      ((∑ q with loopPrimalCluster hN hM A q = c,
        a q * loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q : ℤ) : ℚ) := by
  classical
  simp only [Int.cast_sum,Int.cast_mul]
  simp_rw [← loopBoundaryCycle_windingY hN hM hMp j A]
  rw [ha]
  simp only [diamondWindingY,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- If b divides the winding of every incident loop, it divides the winding
of every integral conserved chain in that cluster. Rational span alone would
not justify this divisibility; the integral expansion does. -/
theorem windingY_multiple_of_incident_loop_windings
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (j : Fin M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) (b : ℤ)
    (hb : ∀ q : Loop hN hM (rcSmoothing A), loopPrimalCluster hN hM A q = c →
      b ∣ loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q)
    (f : diamondCycleSpace hN hM A) (hf : f ∈ ribbonBoundarySpace hN hM A)
    (hs : SupportedOnDiamondCluster hN hM A c f)
    (hint : ∀ e : OpenDiamondEdge A, ∃ z : ℤ, f.val e = z) :
    ∃ z : ℤ, diamondWindingY A f.val = ((b*z : ℤ) : ℚ) := by
  classical
  obtain ⟨a,ha⟩ := exists_integral_loop_expansion_supported hN hM A c f hf hs hint
  have hd : b ∣ ∑ q with loopPrimalCluster hN hM A q = c,
      a q * loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q := by
    apply Finset.dvd_sum
    intro q hq
    exact dvd_mul_of_dvd_right (hb q (Finset.mem_filter.1 hq).2) _
  obtain ⟨z,hz⟩ := hd
  refine ⟨z,?_⟩
  rw [windingY_eq_sum_of_loop_expansion hN hM hMp j A c f a ha,hz]

end
end PottsDiscontinuity.TorusTopology
