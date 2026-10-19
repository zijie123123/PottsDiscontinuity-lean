module

public import PottsDiscontinuity.Bethe.AsymptoticInterpolation

/-! # Arzelà--Ascoli applied to continuous offset envelopes -/

@[expose] public section

open Set Filter
open scoped Topology BoundedContinuousFunction

namespace PottsDiscontinuity.Bethe

theorem exists_uniformly_convergent_subseq_of_lipschitz
    (F : ℕ → ℝ → ℝ) (K : NNReal) (hLip : ∀ i, LipschitzWith K (F i))
    (B : ℝ) (hBound : ∀ i, ∀ x ∈ Icc (-Real.pi) Real.pi, |F i x| ≤ B) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun i x => F (φ i) x) f atTop (Icc (-Real.pi) Real.pi) := by
  let X := Icc (-Real.pi) Real.pi
  let G : ℕ → X →ᵇ ℝ := fun i => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => F i x, (hLip i).continuous.comp continuous_subtype_val⟩
  let A : Set (X →ᵇ ℝ) := range G
  have hALip (g : A) : LipschitzWith K (fun x : X => g.val x) := by
    obtain ⟨i, hi⟩ := g.property
    rw [← hi]
    change LipschitzWith K (fun x : X => F i x)
    simpa only [mul_one, Function.comp_def] using (hLip i).comp (LipschitzWith.subtype_val X)
  have hEqui : Equicontinuous (fun g : A => fun x : X => g.val x) :=
    (LipschitzWith.uniformEquicontinuous _ K hALip).equicontinuous
  have hComp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc A
      (fun g x hg => by
        obtain ⟨i, rfl⟩ := hg
        exact abs_le.mp (hBound i x x.property)) hEqui
  obtain ⟨f, _, φ, hφ, ht⟩ := hComp.tendsto_subseq (fun i => subset_closure ⟨i, rfl⟩)
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  refine ⟨IccExtend hpi (fun x => f x), continuous_IccExtend_iff.mpr f.continuous, φ, hφ, ?_⟩
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ht
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with i hi x hx
  rw [IccExtend_of_mem hpi _ hx]
  exact hi ⟨x, hx⟩

theorem rootOffsetExtension_bound {n : ℕ} (hn : 0 < n) (q u : Fin n → ℝ)
    (K : NNReal) {B x : ℝ} (hq : ∀ j, q j ∈ Icc (-Real.pi) Real.pi)
    (hu : ∀ j, |u j| ≤ B) (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |rootOffsetExtension hn q u K x| ≤ B + (K : ℝ) * (2 * Real.pi) := by
  apply abs_le.mpr
  constructor
  · apply Finset.le_inf'
    intro j _
    have := (abs_le.mp (hu j)).1
    have := mul_nonneg K.coe_nonneg (abs_nonneg (x - q j))
    have := mul_nonneg K.coe_nonneg (show 0 ≤ 2 * Real.pi by positivity)
    linarith
  · let j : Fin n := ⟨0, hn⟩
    have he : rootOffsetExtension hn q u K x ≤ u j + K * |x - q j| :=
      Finset.inf'_le _ (Finset.mem_univ j)
    have hd : |x - q j| ≤ 2 * Real.pi := abs_le.mpr ⟨by linarith [(hq j).2, hx.1],
      by linarith [(hq j).1, hx.2]⟩
    have := mul_le_mul_of_nonneg_left hd K.coe_nonneg
    have := (abs_le.mp (hu j)).2
    linarith

/-- A genuine compactness statement for the discontinuous source offsets:
apply Arzelà--Ascoli to the canonical continuous envelopes, then transfer
uniform convergence using the vanishing mesh. -/
theorem exists_offset_subseq_of_geometry (r : ℕ) (N : ℕ → ℕ)
    (h4 : ∀ i, 4 ∣ N i) (hr : ∀ i, r ≤ N i / 2) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hq : ∀ i, q i ∈ S_n (N i / 2 - r)) (K : NNReal) (B : ℝ)
    (hbound : ∀ i j, |offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) j| ≤ B)
    (hpair : ∀ i j k,
      |offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) j -
        offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) k| ≤ (K : ℝ) * |q i j - q i k|)
    (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0))
    (hmesh : ∀ i, ∀ j : Fin (N i / 2 - r + 1),
      rootPartitionPoint (N i / 2 - r) (q i) (hn i) j.succ -
        rootPartitionPoint (N i / 2 - r) (q i) (hn i) j.castSucc ≤ d i) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun i x => offsetFunction (N (φ i)) r (h4 (φ i)) (hr (φ i))
        (p (φ i)) (q (φ i)) (hn (φ i)) x) f atTop (Icc (-Real.pi) Real.pi) := by
  let G : ℕ → ℝ → ℝ := fun i => rootOffsetExtension (hn i) (q i)
    (offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i)) K
  have hGLip (i : ℕ) : LipschitzWith K (G i) := rootOffsetExtension_lipschitz _ _ _ _
  have hGBound : ∀ i, ∀ x ∈ Icc (-Real.pi) Real.pi, |G i x| ≤ B + (K : ℝ) * (2 * Real.pi) := by
    intro i x hx
    exact rootOffsetExtension_bound (hn i) (q i) _ K
      (fun j => ⟨((hq i).1 j).1.le, ((hq i).1 j).2.le⟩) (hbound i) hx
  obtain ⟨f, hf, φ, hφ, hlim⟩ := exists_uniformly_convergent_subseq_of_lipschitz G K hGLip _ hGBound
  refine ⟨f, hf, φ, hφ, ?_⟩
  have hE : Tendsto (fun i => (K : ℝ) * d (φ i)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using (hd.comp hφ.tendsto_atTop).const_mul (K : ℝ)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (ε / 2) (by positivity),
    hE.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))] with i hi hEi x hx
  have hclose := offsetFunction_sub_extension_le (h4 (φ i)) (hr (φ i)) (hn (φ i))
    (hq (φ i)) K (hpair (φ i)) (hmesh (φ i)) hx
  have htri := dist_triangle (f x) (G (φ i) x)
    (offsetFunction (N (φ i)) r (h4 (φ i)) (hr (φ i)) (p (φ i)) (q (φ i)) (hn (φ i)) x)
  have hnear := hi x hx
  simp only [Real.dist_eq] at htri hnear ⊢
  change |offsetFunction (N (φ i)) r (h4 (φ i)) (hr (φ i)) (p (φ i)) (q (φ i)) (hn (φ i)) x -
    G (φ i) x| ≤ _ at hclose
  rw [abs_sub_comm _ (G (φ i) x)] at hclose
  linarith only [htri, hnear, hclose, hEi]

end PottsDiscontinuity.Bethe
