module

public import Mathlib
public import PottsDiscontinuity.AnalyticTools.Implicit

/-! # Local sections in an admissible state region -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

/-- An interior regular zero has a continuous local section in the state
region, with the local uniqueness needed by compact continuation. The auxiliary
section is extended outside its local domain by the base state; the equation
is asserted only locally. -/
theorem local_section_of_analytic_regular_interior_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Set ℝ} {C : Set E} {F : ℝ × E → E}
    (t : P) (x : C) (hF : AnalyticAt ℝ F (t.val, x.val))
    (hzero : F (t.val, x.val) = 0) (hx : x.val ∈ interior C)
    (e : E ≃L[ℝ] E)
    (he : (fderiv ℝ F (t.val, x.val)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      (e : E →L[ℝ] E)) :
    ∃ φ : P → C, ContinuousAt φ t ∧ φ t = x ∧
      (∀ᶠ u in 𝓝 t, F (u.val, (φ u).val) = 0) ∧
      ∃ W : Set (P × C), IsOpen W ∧ (t, x) ∈ W ∧
        ∀ u y, (u, y) ∈ W → F (u.val, y.val) = 0 → y = φ u := by
  classical
  obtain ⟨ψ, hψbase, hψanalytic, W, V, hWopen, hVopen, hWbase, hVbase, hbranch, hunique⟩ :=
    PottsDiscontinuity.AnalyticTools.exists_analytic_implicitFunction_with_local_uniqueness
      hF hzero e he
  have hψC : ∀ᶠ u in 𝓝 t.val, ψ u ∈ C := by
    have hn : C ∈ 𝓝 (ψ t.val) := by rw [hψbase]; exact mem_interior_iff_mem_nhds.mp hx
    exact hψanalytic.continuousAt.eventually hn
  have hsub : ContinuousAt (Subtype.val : P → ℝ) t := continuous_subtype_val.continuousAt
  have hnearC : ∀ᶠ u : P in 𝓝 t, ψ u.val ∈ C := hsub.eventually hψC
  let φ : P → C := fun u => if h : ψ u.val ∈ C then ⟨ψ u.val, h⟩ else x
  have hφeq : (fun u : P => (φ u).val) =ᶠ[𝓝 t] fun u => ψ u.val := by
    filter_upwards [hnearC] with u hu
    simp only [φ, dite_eq_left hu]
  have hvalcont : ContinuousAt (fun u : P => (φ u).val) t :=
    (hψanalytic.continuousAt.comp hsub).congr_of_eventuallyEq hφeq
  have hφcont : ContinuousAt φ t := tendsto_subtype_rng.mpr hvalcont
  have hφbase : φ t = x := by
    apply Subtype.ext
    have hC : ψ t.val ∈ C := hψbase ▸ x.property
    simp only [φ, dite_eq_left hC, hψbase]
  let f : P × C → ℝ × E := fun z => (z.1.val, z.2.val)
  have hf : Continuous f := by fun_prop
  refine ⟨φ, hφcont, hφbase, ?_, f ⁻¹' W, hWopen.preimage hf, hWbase, ?_⟩
  · have hnearV : ∀ᶠ u : P in 𝓝 t, u.val ∈ V := hsub.eventually (hVopen.mem_nhds hVbase)
    filter_upwards [hnearV, hφeq] with u hu heq
    rw [heq]
    exact (hbranch _ hu).2
  · intro u y hy hroot
    have hyψ : y.val = ψ u.val := hunique u.val y.val hy hroot
    have hC : ψ u.val ∈ C := hyψ ▸ y.property
    apply Subtype.ext
    simpa only [φ, dite_eq_left hC] using hyψ

end PottsDiscontinuity.Bethe
