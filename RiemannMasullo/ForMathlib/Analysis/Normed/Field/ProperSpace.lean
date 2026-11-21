module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocalAtTarget

@[expose] public section

namespace RiemannMasullo

open Function Set Topology
open scoped NNReal

/-- On the units of a proper normed field, every positive natural power of the norm is proper. -/
theorem isProperMap_units_nnNorm_pow {K : Type*} [NormedField K] [ProperSpace K]
    (n : ℕ) (hn : n ≠ 0) :
    IsProperMap ((Units.map nnNormHom.toMonoidHom) ^ n : Kˣ →* ℝ≥0ˣ) := by
  let f (x : K) := ‖x‖₊ ^ n
  have hnorm : IsProperMap (fun x : K ↦ ‖x‖₊) := by
    simpa only [show (nndist (0 : K)) = (fun x ↦ ‖x‖₊) from funext nndist_zero_left] using
      isProperMap_nndist (0 : K)
  have hf : IsProperMap f := (NNReal.powOrderIso n hn).toHomeomorph.isProperMap.comp hnorm
  let s := {t : ℝ≥0 | t ≠ 0}
  have hpre : {x : K | x ≠ 0} = f ⁻¹' s := by
    ext x
    simp [f, s, hn]
  let e := (unitsHomeomorphNeZero (G₀ := K)).trans (Homeomorph.setCongr hpre)
  let u : Kˣ →* ℝ≥0ˣ := (Units.map nnNormHom.toMonoidHom) ^ n
  have hu : Continuous u := (continuous_nnNorm.units_map nnNormHom.toMonoidHom).pow n
  apply isProperMap_of_comp_of_inj hu (unitsHomeomorphNeZero (G₀ := ℝ≥0)).continuous _
    (unitsHomeomorphNeZero (G₀ := ℝ≥0)).injective
  exact (hf.restrictPreimage s).comp e.isProperMap

end RiemannMasullo
