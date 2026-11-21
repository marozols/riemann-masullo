module

public import Mathlib.Analysis.Complex.PhragmenLindelof

/-! # Polynomially weighted bounds on vertical strips -/

public section
namespace RiemannMasullo

open Filter Set Topology

/-- A bounded holomorphic function with polynomially weighted bounds on the two edges
of a vertical strip satisfies the same weighted bound throughout the strip. -/
theorem norm_pow_mul_le_on_verticalStrip {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hF : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo a b)) {M : ℝ}
    (hM : ∀ z : ℂ, z.re ∈ Icc a b → ‖F z‖ ≤ M) (n : ℕ) {C : ℝ}
    (ha : ∀ z : ℂ, z.re = a → ‖z ^ n * F z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖z ^ n * F z‖ ≤ C)
    (z : ℂ) (hz : z.re ∈ Icc a b) : ‖z ^ n * F z‖ ≤ C := by
  let c := Real.pi / (b - a) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : DiffContOnCl ℂ (fun w : ℂ ↦ w ^ n * F w) (Complex.re ⁻¹' Ioo a b) :=
    ⟨(differentiableOn_id.pow n).mul hF.1, (continuousOn_id.pow n).mul hF.2⟩
  apply PhragmenLindelof.vertical_strip hd _ ha hb hz.1 hz.2
  refine ⟨c, half_lt_self (div_pos Real.pi_pos (sub_pos.mpr hab)), 1, ?_⟩
  let R := |a| + |b|
  apply Asymptotics.IsBigO.of_bound (M * (n.factorial / c ^ n) * Real.exp (c * R))
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro w hw
  have hRe : |w.re| ≤ R := by
    change a < w.re ∧ w.re < b at hw
    dsimp [R]
    exact abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b],
      by linarith [le_abs_self b, abs_nonneg a]⟩
  have hn : ‖w‖ ^ n ≤ (n.factorial / c ^ n) * Real.exp (c * ‖w‖) := by
    have h := Real.pow_div_factorial_le_exp _ (mul_nonneg hc.le (norm_nonneg w)) n
    rw [mul_pow, div_le_iff₀ (by positivity)] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith only [h]
  have he : Real.exp (c * ‖w‖) ≤ Real.exp (c * R) * Real.exp (c * |w.im|) := by
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((Complex.norm_le_abs_re_add_abs_im w).trans (add_le_add hRe le_rfl)) hc.le)
  have hM0 := (norm_nonneg (F w)).trans (hM w ⟨hw.1.le, hw.2.le⟩)
  simp only [norm_mul, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
  calc
    ‖w‖ ^ n * ‖F w‖ ≤ ((n.factorial / c ^ n) * Real.exp (c * ‖w‖)) * M :=
      mul_le_mul hn (hM w ⟨hw.1.le, hw.2.le⟩) (norm_nonneg _) (by positivity)
    _ ≤ ((n.factorial / c ^ n) * (Real.exp (c * R) * Real.exp (c * |w.im|))) * M := by gcongr
    _ ≤ _ := by
      have ht := Real.add_one_le_exp (Real.exp (c * |w.im|))
      have ht' : Real.exp (c * |w.im|) ≤ Real.exp (Real.exp (c * |w.im|)) := by linarith
      calc
        _ = (M * (n.factorial / c ^ n) * Real.exp (c * R)) * Real.exp (c * |w.im|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ht' (by positivity)

end RiemannMasullo
