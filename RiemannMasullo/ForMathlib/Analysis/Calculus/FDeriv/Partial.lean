module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open Asymptotics Filter Set Topology

namespace RiemannMasullo

/-- The first-order approximation in a fixed direction is uniform as the base point
approaches a point of continuity of the directional derivative. -/
private theorem isLittleO_line_increment {𝕜 E F α : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f d : E → F} {x v : E} {l : Filter α} {w : α → E} {a : α → 𝕜}
    (hw : Tendsto w l (𝓝 x)) (ha : Tendsto a l (𝓝 0))
    (hd : ∀ᶠ z in 𝓝 x, HasLineDerivAt 𝕜 f (d z) z v) (hc : ContinuousAt d x) :
    (fun u ↦ f (w u + a u • v) - f (w u) - a u • d x) =o[l] a := by
  rw [isLittleO_iff]
  intro ε hε
  have hnear : ∀ᶠ z in 𝓝 x, HasLineDerivAt 𝕜 f (d z) z v ∧ ‖d z - d x‖ < ε :=
    hd.and (by simpa only [Metric.mem_ball, dist_eq_norm] using
      hc.tendsto.eventually (Metric.ball_mem_nhds (d x) hε))
  have hlim : Tendsto (fun p : α × 𝕜 ↦ w p.1 + p.2 • v) (l ×ˢ 𝓝 0) (𝓝 x) := by
    have ht : Tendsto (Prod.snd : α × 𝕜 → 𝕜) (l ×ˢ 𝓝 0) (𝓝 0) := tendsto_snd
    simpa using (hw.comp tendsto_fst).add (ht.smul (tendsto_const_nhds (x := v)))
  obtain ⟨U, hU, T, hT, hUT⟩ := mem_prod_iff.mp (hlim.eventually hnear)
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp hT
  filter_upwards [hU, ha.eventually (Metric.ball_mem_nhds (0 : 𝕜) hδ)] with u hu huδ
  let g (t : 𝕜) := f (w u + t • v) - t • d x
  have hderiv (t : 𝕜) (ht : t ∈ Metric.ball 0 δ) :
      HasDerivAt g (d (w u + t • v) - d x) t := by
    have h := (hUT (show (u, t) ∈ U ×ˢ T from ⟨hu, hδT ht⟩)).1
    have hh : HasDerivAt (fun s : 𝕜 ↦ f (w u + t • v + s • v)) (d (w u + t • v)) (t - t) := by
      rw [sub_self]
      exact h
    have shifted := hh.comp_sub_const t t
    have key (s : 𝕜) : w u + t • v + (s - t) • v = w u + s • v := by
      rw [add_assoc, ← add_smul, add_sub_cancel]
    simpa [g, key, Pi.sub_def] using shifted.sub ((hasDerivAt_id' t).smul_const (d x))
  have hmean := (convex_ball (0 : 𝕜) δ).norm_image_sub_le_of_norm_deriv_le
    (fun t ht ↦ (hderiv t ht).differentiableAt) (fun t ht ↦ by
      rw [(hderiv t ht).deriv]
      exact (hUT (show (u, t) ∈ U ×ˢ T from ⟨hu, hδT ht⟩)).2.le)
    (Metric.mem_ball_self hδ) huδ
  simpa [g, sub_right_comm] using hmean

/-- Continuous derivatives along the standard coordinate vectors give a Fréchet
derivative, obtained by summing the coordinate increments. -/
theorem hasFDerivAt_of_continuous_coordinate_derivatives {𝕜 F ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι] [DecidableEq ι]
    {f : EuclideanSpace 𝕜 ι → F} {x : EuclideanSpace 𝕜 ι}
    (d : ι → EuclideanSpace 𝕜 ι → F)
    (hd : ∀ i, ∀ᶠ z in 𝓝 x, HasLineDerivAt 𝕜 f (d i z) z (EuclideanSpace.single i 1))
    (hc : ∀ i, ContinuousAt (d i) x) :
    HasFDerivAt (𝕜 := 𝕜) f (∑ i, (EuclideanSpace.proj (𝕜 := 𝕜) i).smulRight (d i x)) x := by
  let step (s : Finset ι) (y : EuclideanSpace 𝕜 ι) :=
    x + ∑ i ∈ s, (y i - x i) • EuclideanSpace.single i (1 : 𝕜)
  have hy (i : ι) : Tendsto (fun y : EuclideanSpace 𝕜 ι ↦ y i - x i) (𝓝 x) (𝓝 0) := by
    simpa using ((EuclideanSpace.proj (𝕜 := 𝕜) i).continuous.tendsto x).sub_const (x i)
  have hstep (s : Finset ι) : Tendsto (step s) (𝓝 x) (𝓝 x) := by
    have hsum := tendsto_finsetSum s fun i _ ↦
      (hy i).smul (tendsto_const_nhds (x := EuclideanSpace.single i (1 : 𝕜)))
    simpa [step] using hsum.const_add x
  -- Move one coordinate at a time and add the resulting first-order errors.
  have rem (s : Finset ι) :
      (fun y ↦ f (step s y) - f x - ∑ i ∈ s, (y i - x i) • d i x)
        =o[𝓝 x] (fun y ↦ y - x) := by
    induction s using Finset.induction_on with
    | empty => simp [step]
    | @insert i s hi ih =>
      have h := isLittleO_line_increment (hstep s) (hy i) (hd i) (hc i)
      have hcoord : (fun y : EuclideanSpace 𝕜 ι ↦ y i - x i) =O[𝓝 x] (fun y ↦ y - x) :=
        isBigO_of_le _ fun y ↦ PiLp.norm_apply_le (y - x) i
      apply ((h.trans_isBigO hcoord).add ih).congr' _ EventuallyEq.rfl
      filter_upwards with y
      have hnext : step (insert i s) y = step s y + (y i - x i) • EuclideanSpace.single i 1 := by
        simp only [step, Finset.sum_insert hi]
        abel
      simp only [hnext, Finset.sum_insert hi]
      abel
  have hfull (y : EuclideanSpace 𝕜 ι) : step Finset.univ y = y := by
    have h := (EuclideanSpace.basisFun ι 𝕜).sum_repr (y - x)
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, PiLp.sub_apply] at h
    simp [step, h]
  apply hasFDerivAt_iff_isLittleO.mpr
  simpa only [hfull, sum_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.proj, PiLp.proj_apply, PiLp.sub_apply] using rem Finset.univ

end RiemannMasullo
