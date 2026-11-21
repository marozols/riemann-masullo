module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Linear changes of variables on Schwartz functions -/

@[expose] public noncomputable section

open scoped SchwartzMap

namespace RiemannMasullo

/-- Pullback along a continuous linear equivalence, with pullback by its inverse as inverse. -/
def schwartzChangeVariable (𝕜 : Type*) [RCLike 𝕜]
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    (e : D ≃L[ℝ] E) : 𝓢(E, F) ≃L[𝕜] 𝓢(D, F) where
  __ := SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 e
  invFun := SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 e.symm
  left_inv f := by ext x; change f (e (e.symm x)) = f x; rw [e.apply_symm_apply]
  right_inv f := by ext x; change f (e.symm (e x)) = f x; rw [e.symm_apply_apply]
  continuous_invFun := (SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 e.symm).continuous

end RiemannMasullo
