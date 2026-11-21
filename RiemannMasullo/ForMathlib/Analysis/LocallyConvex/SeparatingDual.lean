module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

@[expose] public section

namespace RiemannMasullo

/-- Complex or real continuous functionals separate points when the underlying real
module is Hausdorff and locally convex. -/
theorem locallyConvexSpace_separatingDual (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E]
    [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E] [T1Space E] :
    SeparatingDual 𝕜 E := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hx
  exact ⟨φ, fun he ↦ by simp [he] at hφ⟩

/-- The continuous dual of a Hausdorff polynormable space over `ℝ` or `ℂ` separates points. -/
theorem polynormableSpace_separatingDual (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [PolynormableSpace 𝕜 E] [T1Space E] : SeparatingDual 𝕜 E := by
  let : Module ℝ E := Module.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup 𝕜 E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  exact locallyConvexSpace_separatingDual 𝕜 E

end RiemannMasullo
