module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Permutations of the directions of an iterated derivative -/

@[expose] public noncomputable section

open scoped ContDiff

namespace RiemannMasullo

/-- Permuting a list of directions leaves the iterated derivative of a smooth real map unchanged. -/
theorem iteratedFDeriv_apply_list_perm {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (v : ι → E) {l r : List ι} (h : l.Perm r) (x : E) :
    iteratedFDeriv ℝ l.length f x (fun i ↦ v (l.get i)) =
      iteratedFDeriv ℝ r.length f x (fun i ↦ v (r.get i)) := by
  let D (s : List ι) (y : E) := iteratedFDeriv ℝ s.length f y (fun i ↦ v (s.get i))
  have hs (s : List ι) : ContDiff ℝ ∞ (D s) :=
    (ContinuousMultilinearMap.apply ℝ _ F (fun i ↦ v (s.get i))).contDiff.comp
      (hf.iteratedFDeriv_right (by simp))
  have hcons (i : ι) (s : List ι) : D (i :: s) = fun y ↦ fderiv ℝ (D s) y (v i) := by
    funext y
    have hy := hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top s.length) y
    exact hy.iteratedFDeriv_succ_apply_left' (m := fun j ↦ v ((i :: s).get j))
  suffices D l = D r from congrFun this x
  induction h with
  | nil => rfl
  | cons i h ih => rw [hcons, hcons, ih]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap i j s =>
    funext y
    have hder (a b : ι) :
        fderiv ℝ (fun z ↦ fderiv ℝ (D s) z (v b)) y (v a) =
          fderiv ℝ (fderiv ℝ (D s)) y (v a) (v b) := by
      let ev := ContinuousLinearMap.apply ℝ F (v b)
      have hdiff := ((hs s).fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
      exact congrArg (fun t : E →L[ℝ] F ↦ t (v a))
        (ev.hasFDerivAt.comp y hdiff.hasFDerivAt).fderiv
    simp only [hcons, hder]
    exact ((hs s).contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

end RiemannMasullo
