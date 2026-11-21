module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Inclusion of fixed-support test functions into Schwartz space -/

@[expose] public noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap

namespace RiemannMasullo

/-- Smooth functions supported in a fixed compact set include continuously into Schwartz space. -/
def supportedToSchwartzCLM (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
    (K : Compacts X) : 𝓓_{K}(X, V) →L[𝕜] 𝓢(X, V) := by
  let J : 𝓓_{K}(X, V) →ₗ[𝕜] 𝓢(X, V) :=
    { toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
      map_add' f g := by ext; rfl
      map_smul' c f := by ext; rfl }
  refine ⟨J, (ContDiffMapSupportedIn.withSeminorms 𝕜 X V ⊤ K).continuous_of_isBounded
    (schwartz_withSeminorms 𝕜 X V) J (Seminorm.IsBounded.of_real ?_)⟩
  obtain ⟨R, hR⟩ := K.isCompact.exists_bound_of_continuousOn (f := id) continuous_id.continuousOn
  rintro ⟨k, n⟩
  refine ⟨{n}, (max R 0) ^ k, fun f ↦ ?_⟩
  rw [Finset.sup_singleton]
  have hnn := apply_nonneg (ContDiffMapSupportedIn.seminorm 𝕜 X V ⊤ K n) f
  apply SchwartzMap.seminorm_le_bound 𝕜 k n _ (mul_nonneg (pow_nonneg (le_max_right R 0) _) hnn)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ _
  by_cases hx : x ∈ K
  · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ((hR x hx).trans (le_max_left R 0)) k)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜)
      (norm_nonneg _) (pow_nonneg (le_max_right R 0) _)
  · rw [f.iteratedFDeriv_zero_on_compl hx]
    simpa using mul_nonneg (pow_nonneg (le_max_right R 0) k) hnn

end RiemannMasullo
