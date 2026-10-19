module

public import Mathlib
public import PottsDiscontinuity.AnalyticTools.Identity

/-!
# Corollary 3.4: analytic spectral tools

This file formalizes the local uniqueness argument for an eigenvalue converging to a simple
top root, the positive-vector pairing criterion, and the real-analytic identity principle on an
interval.
-/

@[expose] public section

open Filter Matrix Set
open scoped Topology

namespace PottsDiscontinuity.SixVertex

/-- Identity theorem on any preconnected real interval, including bounded open intervals and
the source half-line `(-∞, b)`. -/
theorem cor34_identity_theorem_extension
    {f g : ℝ → ℝ} {I V : Set ℝ}
    (hf : AnalyticOnNhd ℝ f I) (hg : AnalyticOnNhd ℝ g I)
    (hI : IsPreconnected I) (hV : IsOpen V) (hVne : V.Nonempty)
    (hVI : V ⊆ I) (hfg : EqOn f g V) : EqOn f g I :=
  AnalyticTools.analytic_eqOn_of_eqOn_open_preconnected hf hg hI hV hVne hVI hfg

end PottsDiscontinuity.SixVertex
