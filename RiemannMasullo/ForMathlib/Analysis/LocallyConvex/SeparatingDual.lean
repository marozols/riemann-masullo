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

/-- A point outside a closed submodule is detected by a continuous functional
that vanishes on the submodule. -/
theorem exists_dual_eq_zero_on_submodule_of_notMem {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E)) {x : E} (hx : x ∉ S) :
    ∃ φ : StrongDual 𝕜 E, φ x ≠ 0 ∧ ∀ y ∈ S, φ y = 0 := by
  obtain ⟨φ, r, hl, hr⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    (S.restrictScalars ℝ).convex hS hx
  have hne : φ x ≠ 0 := by
    intro h
    simpa [h] using (hl 0 S.zero_mem).trans hr
  refine ⟨φ, hne, fun y hy ↦ ?_⟩
  by_contra h
  have hlt := (hl _ (S.smul_mem (φ x / φ y) hy)).trans hr
  simp [map_smul, smul_eq_mul, h] at hlt

end RiemannMasullo
