module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public section

open MeasureTheory

namespace RiemannMasullo

/-- Complex compactly supported tests integrate against the induced Haar measure by
first integrating over the closed subgroup and then over the quotient. -/
theorem integral_inducedMeasure_complex {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [LocallyCompactSpace B] [T2Space B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    [MeasurableSpace C] [BorelSpace C]
    {i : A →* B} {p : B →* C} (h : TopologicalGroup.IsSES i p)
    (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    (f : CompactlySupportedContinuousMap B ℂ) :
    ∫ b, f b ∂(h.inducedMeasure μA μC) = h.integrate μA μC f := by
  have test (L : ℂ →L[ℝ] ℝ) :
      L (∫ b, f b ∂(h.inducedMeasure μA μC)) = L (h.integrate μA μC f) := by
    let ℓ : C(ℂ, ℝ) := ⟨L, L.continuous⟩
    let g := f.compLeft ℓ
    have hg (b : B) : g b = L (f b) :=
      CompactlySupportedContinuousMap.compLeft_apply (g := ℓ) L.map_zero f b
    rw [← L.integral_comp_comm f.integrable, h.integrate_apply,
      ← L.integral_comp_comm (h.pushforward μA f).integrable]
    simp_rw [← hg]
    rw [h.integral_inducedMeasure, h.integrate_apply]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro c
    obtain ⟨b, rfl⟩ := h.isOpenQuotientMap.surjective c
    change h.pushforward μA g (p b) = L (h.pushforward μA f (p b))
    rw [h.pushforward_apply_apply, h.pushforward_apply_apply,
      ← L.integral_comp_comm (h.pullback f b).integrable]
    simp only [h.pullback_def, hg]
  exact Complex.ext (test Complex.reCLM) (test Complex.imCLM)

end RiemannMasullo
