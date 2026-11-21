module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Square integrability on product measures -/

public section

open Filter MeasureTheory Set

namespace RiemannMasullo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_integral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {u : α → E} (hu : MemLp u 2 μ) :
    ‖∫ a, u a ∂μ‖ ^ 2 ≤ μ.real univ * ∫ a, ‖u a‖ ^ 2 ∂μ := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := fun a ↦ ‖u a‖) (g := fun _ ↦ (1 : ℝ))
    Real.HolderConjugate.two_two (by simpa using hu.norm) (memLp_const _)
  have hle : ‖∫ a, u a ∂μ‖ ≤ Real.sqrt (∫ a, ‖u a‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa [Real.sqrt_eq_rpow] using hcs
  calc
    _ ≤ (Real.sqrt (∫ a, ‖u a‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
        Real.sq_sqrt (measureReal_nonneg)]
      exact mul_comm _ _

omit [NormedSpace ℝ E] in
/-- A square-integrable function on a product is square integrable on almost every fiber. -/
theorem memLp_two_prod_left_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [SFinite μ] {ν : Measure β} [SFinite ν] {u : α × β → E}
    (h₂ : MemLp u 2 (μ.prod ν)) : ∀ᵐ b ∂ν, MemLp (fun a ↦ u (a, b)) 2 μ := by
  filter_upwards [h₂.norm.integrable_sq.prod_left_ae, h₂.aestronglyMeasurable.prodMk_right]
    with b hb hmeas
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 hb

/-- Integrating a square-integrable function over a finite-measure factor gives a
square-integrable function on the other factor. -/
theorem memLp_two_integral_prod_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure β} [SFinite ν] {u : α × β → E}
    (h₂ : MemLp u 2 (μ.prod ν)) : MemLp (fun b ↦ ∫ a, u (a, b) ∂μ) 2 ν := by
  have hsq := h₂.norm.integrable_sq
  have hmeas : AEStronglyMeasurable (fun b ↦ ∫ a, u (a, b) ∂μ) ν :=
    h₂.aestronglyMeasurable.prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  apply (hsq.integral_prod_right.const_mul (μ.real univ)).mono'
  · exact hmeas.norm.pow 2
  · filter_upwards [memLp_two_prod_left_ae h₂] with b hb
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact norm_integral_sq_le hb

end RiemannMasullo
