module

public import Mathlib.Analysis.LocallyConvex.HahnBanach

@[expose] public section

namespace RiemannMasullo

/-- Any continuous seminorm on a polynormable space is attained at a given vector
by the absolute value of a continuous linear functional dominated by that seminorm. -/
theorem exists_dual_norm_eq_seminorm {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [PolynormableSpace 𝕜 E]
    (p : Seminorm 𝕜 E) (hp : Continuous p) (z : E) :
    ∃ φ : StrongDual 𝕜 E, (∀ y, ‖φ y‖ ≤ p y) ∧ ‖φ z‖ = p z := by
  by_cases hz : z = 0
  · exact ⟨0, fun _ ↦ by simp, by simp [hz]⟩
  let e := LinearEquiv.toSpanNonzeroSingleton 𝕜 E z hz
  let g := (p z : 𝕜) • e.symm.toLinearMap
  have hb (u : Submodule.span 𝕜 {z}) : ‖g u‖ ≤ p u := by
    obtain ⟨a, rfl⟩ := e.surjective u
    change ‖(p z : 𝕜) * e.symm (e a)‖ ≤ p (a • z)
    rw [e.symm_apply_apply, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p z),
      map_smul_eq_mul, mul_comm]
  obtain ⟨φ, hφ, hbound⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm _ g hp hb
  refine ⟨φ, hbound, ?_⟩
  have h := hφ (e 1)
  change φ ((1 : 𝕜) • z) = (p z : 𝕜) * e.symm (e 1) at h
  simp only [one_smul, e.symm_apply_apply, mul_one] at h
  rw [h, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p z)]

end RiemannMasullo
