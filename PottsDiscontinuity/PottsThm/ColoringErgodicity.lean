module

public import PottsDiscontinuity.PottsThm.ColoringFactor

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology
open PottsDiscontinuity.FK
open PottsDiscontinuity.RCInfinite

noncomputable section

/-- A measurable equivariant factor of the product of two mixing lattice
actions is translation ergodic. -/
theorem mixingProduct_factor_translationErgodic {C : Type*} [MeasurableSpace C]
    {μ : Measure LatticeConfiguration} {ν : Measure (Vertex → C)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : Vertex → LatticeConfiguration → LatticeConfiguration)
    (S : Vertex → (Vertex → C) → (Vertex → C))
    (hTpres : ∀ a, MeasurePreserving (T a) μ μ)
    (hSpres : ∀ a, MeasurePreserving (S a) ν ν)
    (hTmix : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => μ.real (A ∩ (T a) ⁻¹' B)) cofinite
        (𝓝 (μ.real A * μ.real B)))
    (hSmix : ∀ A B : Set (Vertex → C), MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => ν.real (A ∩ (S a) ⁻¹' B)) cofinite
        (𝓝 (ν.real A * ν.real B)))
    (F : LatticeConfiguration × (Vertex → C) → Vertex → C)
    (hF : Measurable F)
    (hFshift : ∀ a z x, F (productShift T S a z) x = F z (x - a)) :
    PottsDiscontinuity.IsTranslationErgodic
      ((μ.prod ν).map F) := by
  classical
  let Q : Vertex → LatticeConfiguration × (Vertex → C) →
      LatticeConfiguration × (Vertex → C) := productShift T S
  have hQmeas (a : Vertex) : Measurable (Q a) := by
    dsimp [Q, productShift]
    exact ((hTpres a).measurable.comp measurable_fst).prodMk
      ((hSpres a).measurable.comp measurable_snd)
  have hQpres (a : Vertex) : MeasurePreserving (Q a) (μ.prod ν) (μ.prod ν) := by
    change MeasurePreserving (Prod.map (T a) (S a)) (μ.prod ν) (μ.prod ν)
    exact (hTpres a).prod (hSpres a)
  have hτmeas (a : Vertex) : Measurable (fun σ : Vertex → C => fun x => σ (x + a)) :=
    measurable_pi_iff.mpr fun x => measurable_pi_apply (x + a)
  constructor
  · intro a
    rw [Measure.map_map (hτmeas a) hF]
    have hcomp : (fun σ : Vertex → C => fun x => σ (x + a)) ∘ F = F ∘ Q (-a) := by
      funext z x
      simpa [Function.comp_apply, sub_neg_eq_add] using (hFshift (-a) z x).symm
    rw [hcomp, ← Measure.map_map hF (hQmeas (-a)), (hQpres (-a)).map_eq]
  · intro A hA hAinv
    let E : Set (LatticeConfiguration × (Vertex → C)) := F ⁻¹' A
    have hE : MeasurableSet E := hF hA
    have hEinv : ∀ a, (Q a) ⁻¹' E = E := by
      intro a
      ext z
      change F (Q a z) ∈ A ↔ F z ∈ A
      have hspin : F (Q a z) = fun x => F z (x - a) := funext (hFshift a z)
      rw [hspin]
      have hinv := Set.ext_iff.mp (hAinv (-a)) (F z)
      have hshiftEq : (fun x => F z (x - a)) = (fun x => F z (x + -a)) := by
        funext x
        simp [sub_eq_add_neg]
      rw [hshiftEq]
      exact hinv
    rcases mixingProduct_invariant_event μ ν T S hTpres hSpres hTmix hSmix hE hEinv with h | h
    · left
      rw [Measure.map_apply hF hA]
      exact h
    · right
      rw [Measure.map_apply hF hA.compl]
      simpa only [E, Set.preimage_compl] using h

end
end PottsDiscontinuity.PottsThm
