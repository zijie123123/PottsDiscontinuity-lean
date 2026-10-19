module

public import PottsDiscontinuity.Potts.CylinderColoring

/-! Edwards–Sokal cylinder kernels as functions of finite observed partitions. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

variable {A V C : Type*}

/-- The free colouring kernel depends only on the observed partition. -/
theorem clusterCylinderProbability_factor (R : Setoid V) (v : A → V) (ξ : A → C) :
    clusterCylinderProbability R v ξ = clusterCylinderProbability (R.comap v) id ξ := by
  rfl

/-- The pinned colouring kernel depends only on the observed marked partition. -/
theorem pinnedClusterCylinderProbability_factor (R : Setoid V) (v : A → V) (ξ : A → C)
    (g : V) (i : C) :
    pinnedClusterCylinderProbability R v ξ g i =
      pinnedClusterCylinderProbability (R.comap (markedMap v g)) some ξ none i := by
  have h : (R.comap (markedMap v g)).comap (markedMap some none) = R.comap (markedMap v g) := by
    apply Setoid.ext
    intro a b
    cases a <;> cases b <;> rfl
  simp only [pinnedClusterCylinderProbability, observedClassCount, h]
  rw [h]

end
end PottsDiscontinuity.Potts
