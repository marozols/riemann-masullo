module

public import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Absolute convergence of the Mellin integral in logarithmic coordinates -/

public section
namespace RiemannMasullo

open Filter MeasureTheory
open scoped Asymptotics

/-- An exponential growth bound becomes a real-power bound after composition with `log`. -/
theorem isBigO_comp_log_rpow_of_isBigO_exp {g : ℝ → ℂ} {c : ℝ} {l L : Filter ℝ}
    (h : g =O[l] (fun x ↦ Real.exp (c * x)))
    (ht : Tendsto Real.log L l) (hpos : ∀ᶠ t in L, 0 < t) :
    (fun t ↦ g (Real.log t)) =O[L] (fun t ↦ t ^ c) := by
  apply (h.comp_tendsto ht).congr' EventuallyEq.rfl
  filter_upwards [hpos] with t ht
  simp only [Function.comp_apply, Real.rpow_def_of_pos ht, mul_comm]

/-- A logarithmic profile has an absolutely convergent Mellin integral at `s` if its
exponential weight at the real part of `s` is integrable on the real line. -/
theorem mellinConvergent_of_integrable_logWeight (f : ℝ → ℂ) (s : ℂ)
    (h : Integrable (fun x : ℝ ↦ (Real.exp (s.re * x) : ℂ) * f x)) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  let phase (x : ℝ) := Complex.exp ((x : ℂ) * (s - s.re))
  have hc : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hunit (x : ℝ) : ‖phase x‖ ≤ 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  apply (integrable_comp_exp _).mp
  apply (h.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hunit)).congr
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [phase, Complex.ofReal_exp, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end RiemannMasullo
