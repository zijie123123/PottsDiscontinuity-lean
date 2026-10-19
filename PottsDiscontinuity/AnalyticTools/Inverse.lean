module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Analytic inverse function theorem

This module records the local analytic inverse theorem in the form needed by the Bethe
equation argument.  Mathlib constructs the local inverse as an `OpenPartialHomeomorph`; its
analyticity follows from the analytic power series of the original map and an invertible
derivative.
-/

public section

namespace PottsDiscontinuity.AnalyticTools

/-- The local inverse of an analytic map between complete real normed spaces is analytic at the
image of the base point whenever its derivative is a continuous linear equivalence. -/
theorem analyticAt_localInverse
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {a : E} {e : E ≃L[ℝ] F}
    (hf : AnalyticAt ℝ f a)
    (hstrict : HasStrictFDerivAt f (e : E →L[ℝ] F) a) :
    AnalyticAt ℝ (hstrict.toOpenPartialHomeomorph f).symm (f a) := by
  let R := hstrict.toOpenPartialHomeomorph f
  have hsource : a ∈ R.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hR : AnalyticAt ℝ (R : E → F) a := by
    simpa [R] using hf
  have hderiv : fderiv ℝ (R : E → F) a = (e : E →L[ℝ] F) := by
    simpa [R] using hstrict.hasFDerivAt.fderiv
  exact R.analyticAt_symm' hsource hR hderiv

end PottsDiscontinuity.AnalyticTools
