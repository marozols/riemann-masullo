module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Compact support stages of the test function space
-/

public section

open TopologicalSpace Topology
open scoped Distributions BoundedContinuousFunction

namespace RiemannMasullo

/-- Including the functions supported on a fixed compact set into the space of test
functions is a topological embedding, for every order of differentiability. -/
theorem isEmbedding_testFunction_ofSupportedIn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {K : Compacts E}
    {n : ℕ∞} (hK : (K : Set E) ⊆ Ω) :
    IsEmbedding (TestFunction.ofSupportedIn hK : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)) := by
  -- The bounded derivative depends only on the function, even when several stages contain it.
  let D (i : ℕ) (f : 𝓓^{n}(Ω, F)) : E →ᵇ (E [×i]→L[ℝ] F) :=
    ContDiffMapSupportedIn.structureMapCLM ℝ n i
      (K := ⟨tsupport f, f.hasCompactSupport⟩)
      (.of_support_subset f.contDiff subset_closure)
  have agree (i : ℕ) (J : Compacts E) (hJ : (J : Set E) ⊆ Ω) (f : 𝓓^{n}_{J}(E, F)) :
      D i (TestFunction.ofSupportedIn hJ f) = ContDiffMapSupportedIn.structureMapCLM ℝ n i f := by
    apply DFunLike.coe_injective
    simp only [D, ContDiffMapSupportedIn.structureMapCLM_apply]
    rfl
  let (i : ℕ) : IsTopologicalAddGroup (E →ᵇ (E [×i]→L[ℝ] F)) :=
    @SeminormedAddCommGroup.toIsTopologicalAddGroup (E →ᵇ (E [×i]→L[ℝ] F)) inferInstance
  let (i : ℕ) : LocallyConvexSpace ℝ (E →ᵇ (E [×i]→L[ℝ] F)) :=
    NormedSpace.toLocallyConvexSpace (E := E →ᵇ (E [×i]→L[ℝ] F))
  let T (i : ℕ) : 𝓓^{n}(Ω, F) →L[ℝ] E →ᵇ (E [×i]→L[ℝ] F) :=
    TestFunction.limitCLM ℝ (D i)
      (fun _ _ ↦ ContDiffMapSupportedIn.structureMapCLM ℝ n i) (agree i)
  apply IsEmbedding.of_comp (TestFunction.continuous_ofSupportedIn hK)
    (ContinuousLinearMap.pi T).continuous
  have heq : (ContinuousLinearMap.pi T) ∘ TestFunction.ofSupportedIn hK =
      (ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM ℝ n) :
        𝓓^{n}_{K}(E, F) →L[ℝ] _) := by
    funext f i
    exact agree i K hK f
  rw [heq]
  exact (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ).isEmbedding

end RiemannMasullo
