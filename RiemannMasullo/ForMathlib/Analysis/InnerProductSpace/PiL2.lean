module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! # Bounds for multilinear maps on finite Euclidean spaces -/

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The norm of a multilinear map on finite Euclidean spaces is bounded by the sum
of its norms on coordinate basis tuples. -/
theorem norm_multilinear_le_sum_euclidean_basis {ι κ F : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : ι ↦ EuclideanSpace ℝ κ) F) :
    ‖T‖ ≤ ∑ t : ι → κ, ‖T (fun i ↦ EuclideanSpace.single (t i) 1)‖ := by
  classical
  let e (j : κ) := EuclideanSpace.single j (1 : ℝ)
  apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  have hv (i : ι) : (∑ j, v i j • e j) = v i := by
    simpa [e] using (EuclideanSpace.basisFun κ ℝ).sum_repr (v i)
  have hT : T v = ∑ t : ι → κ, (∏ i, v i (t i)) • T (fun i ↦ e (t i)) := by
    calc
      T v = T.toMultilinearMap (fun i ↦ ∑ j, v i j • e j) := by simp only [hv]; rfl
      _ = _ := by
        rw [T.toMultilinearMap.map_sum (fun i j ↦ v i j • e j)]
        exact Finset.sum_congr rfl fun t _ ↦ T.toMultilinearMap.map_smul_univ _ _
  rw [hT, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
  rw [norm_smul, norm_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ PiLp.norm_apply_le _ _))
    (norm_nonneg _)

end RiemannMasullo
