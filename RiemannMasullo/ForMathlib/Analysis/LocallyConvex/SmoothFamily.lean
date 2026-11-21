module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! # Derivatives of smooth families of linear functionals -/

@[expose] public noncomputable section

open Filter Topology
open scoped ContDiff

namespace RiemannMasullo

/-- If evaluations of a smooth family are continuous linear functionals on a barrelled space,
then evaluating any iterated derivative in fixed directions is a continuous linear functional. -/
theorem exists_clm_iteratedFDeriv_apply
    {U X : Type*} [AddCommGroup U] [Module ℂ U] [UniformSpace U]
    [IsUniformAddGroup U] [ContinuousSMul ℂ U] [BarrelledSpace ℂ U]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (A : X → U →L[ℂ] ℂ)
    (hA : ∀ u, ContDiff ℝ ∞ (fun x ↦ A x u)) (k : ℕ) (x : X) (v : Fin k → X) :
    ∃ L : U →L[ℂ] ℂ, ∀ u, L u = iteratedFDeriv ℝ k (fun y ↦ A y u) x v := by
  induction k generalizing x with
  | zero => exact ⟨A x, fun _ ↦ rfl⟩
  | succ k ih =>
    choose B hB using fun y ↦ ih y (Fin.tail v)
    let D (t : ℝ) : U →L[ℂ] ℂ := t⁻¹ • (B (x + t • v 0) - B x)
    let d (u : U) := iteratedFDeriv ℝ (k + 1) (fun y ↦ A y u) x v
    have hlim : Tendsto (fun t u ↦ D t u) (𝓝[≠] 0) (𝓝 d) := by
      rw [tendsto_pi_nhds]
      intro u
      have hk : DifferentiableAt ℝ (iteratedFDeriv ℝ k (fun y ↦ A y u)) x :=
        (hA u).differentiable_iteratedFDeriv (mod_cast WithTop.coe_lt_top _) x
      have he := (hk.continuousMultilinear_apply_const (Fin.tail v)).hasFDerivAt.hasLineDerivAt (v 0)
      simpa only [D, d, smul_apply, sub_apply, hB,
        hk.iteratedFDeriv_succ_apply_left'] using he.tendsto_slope_zero
    exact ⟨continuousLinearMapOfTendsto (f := d) D hlim, fun _ ↦ rfl⟩

end RiemannMasullo
