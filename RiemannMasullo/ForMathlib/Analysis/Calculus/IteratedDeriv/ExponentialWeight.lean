module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Weighted bounds for derivatives of an exponential twist -/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace RiemannMasullo

/-- Leibniz's formula for an exponential twist, with a polynomial weight outside the norm. -/
theorem norm_iteratedDeriv_exp_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t x : ℝ) (k n : ℕ) (f : ℝ → E) (hf : ContDiff ℝ n f) :
    |x| ^ k * ‖iteratedDeriv n ((fun y ↦ Real.exp (t * y)) • f) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * |t| ^ i) *
        (|x| ^ k * Real.exp (t * x) * ‖iteratedDeriv (n - i) f x‖) := by
  have he : ContDiff ℝ n (fun y : ℝ ↦ Real.exp (t * y)) := by fun_prop
  have hd := iteratedDerivWithin_smul (mem_univ x) uniqueDiffOn_univ
    he.contDiffAt.contDiffWithinAt hf.contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ, iteratedDeriv_exp_const_mul] at hd
  rw [hd]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg x) k)).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [RCLike.norm_nsmul (K := ℝ), nsmul_eq_mul, norm_smul, norm_mul, norm_pow,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  exact le_of_eq (by ring)

end RiemannMasullo
