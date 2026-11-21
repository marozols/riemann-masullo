module

public import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.Compact

@[expose] public section

namespace RiemannMasullo

open Function Set Topology

/-- A complex character of an infinite cyclic group times a compact group is determined
by its value on the generator and its unitary restriction. -/
theorem exists_cyclicProductCharacterHomeomorph {U : Type*} [CommGroup U] [TopologicalSpace U]
    [IsTopologicalGroup U] [CompactSpace U] [T2Space U] :
    ∃ e : (Multiplicative ℤ × U →ₜ* ℂ) ≃ₜ ℂˣ × PontryaginDual U, ∀ c,
      ((e c).1 : ℂ) = c (Multiplicative.ofAdd 1, 1) ∧ ∀ u, ((e c).2 u : ℂ) = c (1, u) := by
  let gen : Multiplicative ℤ × U := (Multiplicative.ofAdd 1, 1)
  let i : U →ₜ* (Multiplicative ℤ × U) :=
    { toFun := fun u ↦ (1, u)
      map_one' := rfl
      map_mul' := fun x y ↦ Prod.ext (mul_one _).symm rfl
      continuous_toFun := continuous_const.prodMk continuous_id }
  have hcircle (c : Multiplicative ℤ × U →ₜ* ℂ) (u : U) :
      c (i u) ∈ Submonoid.unitSphere ℂ := by
    let a := c.comp i
    obtain ⟨B, hB⟩ := (isCompact_range a.continuous.norm).bddAbove
    have hle (v : U) : ‖a v‖ ≤ 1 := by
      by_contra! h
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
      have hb := hB (Set.mem_range_self (v ^ n))
      change ‖a (v ^ n)‖ ≤ B at hb
      rw [map_pow, norm_pow] at hb
      exact hn.not_ge hb
    apply mem_sphere_zero_iff_norm.mpr
    refine (hle u).antisymm ?_
    have h := hle u⁻¹
    rw [map_inv, norm_inv] at h
    exact (inv_le_one₀ (norm_pos_iff.mpr ((Group.isUnit _).map a).ne_zero)).mp h
  let value (c : Multiplicative ℤ × U →ₜ* ℂ) : ℂˣ :=
    Units.mk0 (c gen) ((Group.isUnit gen).map c).ne_zero
  let restrict (c : Multiplicative ℤ × U →ₜ* ℂ) : PontryaginDual U :=
    { toFun := fun u ↦ ⟨c (i u), hcircle c u⟩
      map_one' := Circle.ext (map_one (c.comp i))
      map_mul' := fun u v ↦ Circle.ext (map_mul (c.comp i) u v)
      continuous_toFun := (c.continuous.comp i.continuous).subtype_mk (hcircle c) }
  have hpowers : Continuous (fun p : ℂˣ × Multiplicative ℤ ↦ (p.1 ^ p.2.toAdd : ℂˣ)) :=
    continuous_prod_of_discrete_right.mpr fun n ↦ continuous_zpow n.toAdd
  let extend (p : ℂˣ × PontryaginDual U) : Multiplicative ℤ × U →ₜ* ℂ :=
    { toFun := fun x ↦ ((p.1 ^ x.1.toAdd : ℂˣ) : ℂ) * (p.2 x.2 : ℂ)
      map_one' := by
        change ↑(p.1 ^ (0 : ℤ)) * (p.2 1 : ℂ) = 1
        simp
      map_mul' := fun x y ↦ by
        change ↑(p.1 ^ (x.1.toAdd + y.1.toAdd)) * (p.2 (x.2 * y.2) : ℂ) = _
        simp only [zpow_add, Units.val_mul, map_mul, Circle.coe_mul]
        ring
      continuous_toFun := (Units.continuous_val.comp (hpowers.comp
        (continuous_const.prodMk continuous_fst))).mul
        (continuous_subtype_val.comp (p.2.continuous.comp continuous_snd)) }
  refine ⟨{
    toFun := fun c ↦ (value c, restrict c)
    invFun := extend
    left_inv := fun c ↦ by
      ext1 x
      have hgen : gen ^ x.1.toAdd * i x.2 = x := by
        apply Prod.ext
        · change x.1.toAdd • (1 : ℤ) + 0 = x.1.toAdd
          simp
        · change (1 : U) ^ x.1.toAdd * x.2 = x.2
          simp
      change ↑(value c ^ x.1.toAdd) * c (i x.2) = c x
      rw [Units.val_zpow_eq_zpow_val]
      change (c gen) ^ x.1.toAdd * c (i x.2) = c x
      rw [← map_zpow, ← map_mul, hgen]
    right_inv := fun p ↦ Prod.ext (Units.ext (by
      change ↑(p.1 ^ (1 : ℤ)) * (p.2 1 : ℂ) = _
      simp)) (PontryaginDual.ext fun u ↦ Circle.ext (by
        change ↑(p.1 ^ (0 : ℤ)) * (p.2 u : ℂ) = _
        simp))
    continuous_toFun := (Units.isEmbedding_val₀.continuous_iff.mpr (continuous_eval_const gen)).prodMk ?_
    continuous_invFun := ContinuousMonoidHom.continuous_of_continuous_uncurry extend ?_ },
    fun c ↦ ⟨rfl, fun u ↦ rfl⟩⟩
  · apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (continuous_eval.comp (continuous_fst.prodMk (i.continuous.comp continuous_snd))).subtype_mk
      (fun p ↦ hcircle p.1 p.2)
  · have : ContinuousEval (PontryaginDual U) U Circle :=
      inferInstanceAs (ContinuousEval (U →ₜ* Circle) U Circle)
    exact (Units.continuous_val.comp (hpowers.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)))).mul (continuous_subtype_val.comp
      (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd))))

end RiemannMasullo
