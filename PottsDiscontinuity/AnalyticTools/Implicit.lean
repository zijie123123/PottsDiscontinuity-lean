module

public import PottsDiscontinuity.AnalyticTools.Inverse

/-!
# Real analytic implicit functions in finite dimension

For an equation `F (t, x) = 0`, the map `(t, x) ↦ (t, F (t, x))` has an invertible derivative
whenever the derivative of `F` in `x` is invertible.  Applying the analytic inverse theorem to
that map gives a local analytic solution branch.
-/

public section

open Filter
open scoped Topology

namespace PottsDiscontinuity.AnalyticTools

noncomputable def parameterShear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ →L[ℝ] E) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toFun p := (p.1, A p.1 + p.2)
  invFun p := (p.1, p.2 - A p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by
    change (p.1 + q.1, A (p.1 + q.1) + (p.2 + q.2)) =
      (p.1 + q.1, A p.1 + p.2 + (A q.1 + q.2))
    rw [map_add]
    congr 1
    abel
  map_smul' c p := by
    change (c • p.1, A (c • p.1) + c • p.2) =
      (c • p.1, c • (A p.1 + p.2))
    rw [map_smul, smul_add]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A finite-dimensional real analytic implicit function theorem with a one-dimensional
parameter.  The branch is defined on all of `ℝ` by the local inverse's totalized inverse map;
the equation is asserted on a neighborhood of the base parameter. -/
theorem exists_analytic_implicitFunction_with_local_uniqueness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ × E → E}
    {t₀ : ℝ} {x₀ : E}
    (hF : AnalyticAt ℝ F (t₀, x₀))
    (hzero : F (t₀, x₀) = 0)
    (e : E ≃L[ℝ] E)
    (hDx : (fderiv ℝ F (t₀, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      (e : E →L[ℝ] E)) :
    ∃ ψ : ℝ → E,
      ψ t₀ = x₀ ∧ AnalyticAt ℝ ψ t₀ ∧
      ∃ W : Set (ℝ × E), ∃ V : Set ℝ,
        IsOpen W ∧ IsOpen V ∧ (t₀, x₀) ∈ W ∧ t₀ ∈ V ∧
        (∀ t ∈ V, (t, ψ t) ∈ W ∧ F (t, ψ t) = 0) ∧
        (∀ t y, (t, y) ∈ W → F (t, y) = 0 → y = ψ t) := by
  let z₀ : ℝ × E := (t₀, x₀)
  let D : (ℝ × E) →L[ℝ] E := fderiv ℝ F z₀
  let A : ℝ →L[ℝ] E := D.comp (ContinuousLinearMap.inl ℝ ℝ E)
  let J : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) e).trans
      (parameterShear A)
  let g : ℝ × E → ℝ × E := fun z => (z.1, F z)
  let Dg : (ℝ × E) →L[ℝ] (ℝ × E) :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod D
  have hsplit (z : ℝ × E) : D z = A z.1 + (e : E →L[ℝ] E) z.2 := by
    have hz : z = ContinuousLinearMap.inl ℝ ℝ E z.1 +
        ContinuousLinearMap.inr ℝ ℝ E z.2 := by
      ext <;> simp [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
    rw [hz, map_add]
    simp only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
      Prod.fst_add, Prod.snd_add, zero_add, add_zero]
    change D (z.1, 0) + D (0, z.2) = D (z.1, 0) + e z.2
    congr 1
    have hb := congrArg (fun L : E →L[ℝ] E => L z.2) hDx
    have harg : (ContinuousLinearMap.inr ℝ ℝ E) z.2 = (0, z.2) := rfl
    rw [← harg]
    exact hb
  have hJ (z : ℝ × E) : J z = (z.1, A z.1 + e z.2) := by
    simp [J, parameterShear]
  have hDg (z : ℝ × E) : Dg z = (z.1, D z) := by
    simp [Dg]
  have hlin : Dg = (J : (ℝ × E) →L[ℝ] (ℝ × E)) := by
    apply DFunLike.ext
    intro z
    change Dg z = J z
    rw [hDg z, hJ z, hsplit z]
    rfl
  have hGanalytic : AnalyticAt ℝ g z₀ := by
    exact analyticAt_fst.prod hF
  have hGstrict : HasStrictFDerivAt g (J : (ℝ × E) →L[ℝ] (ℝ × E)) z₀ := by
    have h : HasStrictFDerivAt g Dg z₀ := by
      change HasStrictFDerivAt (fun z => (z.1, F z)) Dg z₀
      exact (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := z₀)).prodMk hF.hasStrictFDerivAt
    rw [hlin] at h
    exact h
  have hzero' : g z₀ = (t₀, 0) := by simp [g, z₀, hzero]
  have hinverse := analyticAt_localInverse hGanalytic hGstrict
  let R := hGstrict.toOpenPartialHomeomorph g
  let q : ℝ → ℝ × E := fun t => (t, 0)
  let pairBranch : ℝ → ℝ × E := R.symm ∘ q
  let ψ : ℝ → E := fun t => (pairBranch t).2
  have hsource : z₀ ∈ R.source := hGstrict.mem_toOpenPartialHomeomorph_source
  have hψ₀ : ψ t₀ = x₀ := by
    have hqbase : q t₀ = g z₀ := by simp [q, g, z₀, hzero]
    have hleft : R.symm (q t₀) = z₀ := by
      simpa [R, hqbase] using R.left_inv hsource
    simp [ψ, pairBranch, z₀, hleft]
  have hq : AnalyticAt ℝ q t₀ := by fun_prop
  have hinverse' : AnalyticAt ℝ R.symm (t₀, (0 : E)) := by
    simpa [R, g, z₀, hzero] using hinverse
  have hpair : AnalyticAt ℝ pairBranch t₀ := by
    exact hinverse'.comp_of_eq hq (by simp [q])
  have hψanalytic : AnalyticAt ℝ ψ t₀ := by
    change AnalyticAt ℝ (fun t => (pairBranch t).2) t₀
    exact (analyticAt_snd (𝕜 := ℝ) (p := pairBranch t₀)).comp hpair
  have himage : g z₀ ∈ R.target := hGstrict.image_mem_toOpenPartialHomeomorph_target
  have hqtarget : (t₀, (0 : E)) ∈ R.target := by simpa [← hzero'] using himage
  have hqcontinuous : Continuous q := by fun_prop
  let V : Set ℝ := q ⁻¹' R.target
  have hopenV : IsOpen V := IsOpen.preimage hqcontinuous R.open_target
  have hbaseV : t₀ ∈ V := hqtarget
  refine ⟨ψ, hψ₀, hψanalytic, R.source, V, R.open_source, hopenV, hsource, hbaseV, ?_, ?_⟩
  · intro t ht
    have htarg : q t ∈ R.target := ht
    have hbranchsource : pairBranch t ∈ R.source := by
      exact R.map_target htarg
    have heq : g (pairBranch t) = q t := by
      simpa [pairBranch, R] using R.right_inv htarg
    have hfst : (pairBranch t).1 = t := by
      simpa [g, q] using congrArg Prod.fst heq
    have hpairEq : pairBranch t = (t, ψ t) := by
      apply Prod.ext
      · exact hfst
      · rfl
    have hsecond : F (pairBranch t) = 0 := by
      simpa [g, q] using congrArg Prod.snd heq
    constructor
    · rw [← hpairEq]
      exact hbranchsource
    · simpa [hpairEq] using hsecond
  · intro t y hyW hyzero
    have hgy : g (t, y) = q t := by simp [g, q, hyzero]
    have hleft := R.left_inv hyW
    change R.symm (g (t, y)) = (t, y) at hleft
    rw [hgy] at hleft
    have hcoord : ψ t = y := by
      simpa [ψ, pairBranch] using congrArg Prod.snd hleft
    exact hcoord.symm

/-- The usual local analytic implicit function theorem, with the equation asserted on a
neighborhood of the base parameter. -/
theorem exists_analytic_implicitFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ × E → E}
    {t₀ : ℝ} {x₀ : E}
    (hF : AnalyticAt ℝ F (t₀, x₀))
    (hzero : F (t₀, x₀) = 0)
    (e : E ≃L[ℝ] E)
    (hDx : (fderiv ℝ F (t₀, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      (e : E →L[ℝ] E)) :
    ∃ ψ : ℝ → E,
      ψ t₀ = x₀ ∧ AnalyticAt ℝ ψ t₀ ∧
      ∀ᶠ t in 𝓝 t₀, F (t, ψ t) = 0 := by
  obtain ⟨ψ, hψ₀, hψanalytic, W, V, hWopen, hVopen, hWbase, hVbase, hbranch, hunique⟩ :=
    exists_analytic_implicitFunction_with_local_uniqueness hF hzero e hDx
  refine ⟨ψ, hψ₀, hψanalytic, ?_⟩
  filter_upwards [hVopen.mem_nhds hVbase] with t ht
  exact (hbranch t ht).2

end PottsDiscontinuity.AnalyticTools
