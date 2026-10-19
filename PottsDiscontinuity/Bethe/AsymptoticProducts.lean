module

public import PottsDiscontinuity.Bethe.AsymptoticOffsetControl

/-! # Root values and products in the uniform limit argument -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem offsetFunction_at_root {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hn : 0 < N / 2 - r) (hq : StrictMono q) (j : Fin (N / 2 - r)) :
    offsetFunction N r h4 hr p q hn (q j) = offsetDisplacement N r h4 hr p q j := by
  by_cases hj : j.val + 1 < N / 2 - r
  · exact offsetFunction_on_cell h4 hr hn hq j hj
      ⟨le_rfl, hq (show j < ⟨j.val + 1, hj⟩ from by change j.val < j.val + 1; omega)⟩
  · have hlast : j = ⟨N / 2 - r - 1, by omega⟩ := Fin.ext (by
      change j.val = N / 2 - r - 1
      omega)
    have hfirst : ¬q j < q ⟨0, hn⟩ := by
      have := hq.monotone (show (⟨0, hn⟩ : Fin (N / 2 - r)) ≤ j from by change 0 ≤ j.val; omega)
      linarith
    rw [hlast] at hfirst ⊢
    simp [offsetFunction, hfirst]

theorem tendstoUniformlyOn_mul_of_bounds {ι : Type*} {l : Filter ι}
    {F G : ι → ℝ → ℝ} {f g : ℝ → ℝ} {s : Set ℝ}
    (hF : TendstoUniformlyOn F f l s) (hG : TendstoUniformlyOn G g l s)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hboundF : ∀ i, ∀ x ∈ s, |F i x| ≤ M) (hboundg : ∀ x ∈ s, |g x| ≤ B) :
    TendstoUniformlyOn (fun i x => F i x * G i x) (fun x => f x * g x) l s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (M + B + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hid : (M + B + 1) * δ = ε := by dsimp [δ]; field_simp
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF δ hδ,
    Metric.tendstoUniformlyOn_iff.mp hG δ hδ] with i hiF hiG x hx
  have h₁ : |F i x - f x| ≤ δ := by
    simpa only [Real.dist_eq, abs_sub_comm] using (hiF x hx).le
  have h₂ : |G i x - g x| ≤ δ := by
    simpa only [Real.dist_eq, abs_sub_comm] using (hiG x hx).le
  have heq : F i x * G i x - f x * g x =
      F i x * (G i x - g x) + (F i x - f x) * g x := by ring
  have hbound : |F i x * G i x - f x * g x| ≤ M * δ + δ * B := by
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul (hboundF i x hx) h₂ (abs_nonneg _) hM)
      (mul_le_mul h₁ (hboundg x hx) (abs_nonneg _) hδ.le)
  rw [Real.dist_eq, abs_sub_comm]
  nlinarith only [hbound, hid, hδ]

end PottsDiscontinuity.Bethe
