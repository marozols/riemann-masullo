module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

namespace RiemannMasullo

open scoped NNReal
local notation "valℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)

/-- Real one-parameter subgroups of the complex exponential determine their exponent. -/
private theorem exp_real_mul_injective {a b : ℂ}
    (h : ∀ x : ℝ, Complex.exp ((x : ℂ) * a) = Complex.exp ((x : ℂ) * b)) : a = b := by
  have he := Complex.isCoveringMap_exp.eq_of_comp_eq
    (Complex.continuous_ofReal.mul (continuous_const (y := a)))
    (Complex.continuous_ofReal.mul (continuous_const (y := b)))
    (funext fun x ↦ Subtype.ext (h x)) 0 (by simp)
  simpa using congrFun he 1

/-- Every continuous complex character of the positive real units is a unique complex power. -/
theorem existsUnique_complexPower (c : ℝ≥0ˣ →ₜ* ℂ) :
    ∃! z : ℂ, ∀ t : ℝ≥0ˣ, c t = (valℝ t : ℂ) ^ z := by
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hE (x : ℝ) : valℝ (E x) = Real.exp x := rfl
  have h0 : E 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hadd (x y : ℝ) : E (x + y) = E x * E y := Units.ext (NNReal.coe_inj.mp (Real.exp_add x y))
  have hpow (x : ℝ) (z : ℂ) : (valℝ (E x) : ℂ) ^ z = Complex.exp ((x : ℂ) * z) := by
    rw [hE, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  let f : C(ℝ, ℂ) := ⟨fun x ↦ c (E x), c.continuous.comp E.continuous⟩
  have hf : Complex.exp 0 = f 0 := by
    change _ = c (E 0)
    simp [h0]
  obtain ⟨L, ⟨hL0, hL⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f hf
    (fun x ↦ ((Group.isUnit (E x)).map c).ne_zero)
  have hLift (x : ℝ) : Complex.exp (L x) = c (E x) := congrFun hL x
  -- The two lifts of the product character agree at the origin.
  have hsum : (fun p : ℝ × ℝ ↦ L (p.1 + p.2)) = fun p ↦ L p.1 + L p.2 := by
    apply Complex.isCoveringMap_exp.eq_of_comp_eq
      (L.continuous.comp (continuous_fst.add continuous_snd))
      ((L.continuous.comp continuous_fst).add (L.continuous.comp continuous_snd)) _ (0, 0)
    · change L (0 + 0) = L 0 + L 0
      simp [hL0]
    · funext p
      apply Subtype.ext
      change Complex.exp (L (p.1 + p.2)) = Complex.exp (L p.1 + L p.2)
      rw [Complex.exp_add, hLift, hLift, hLift, hadd, map_mul]
  let A : ℝ →+ ℂ := ⟨⟨L, hL0⟩, fun x y ↦ congrFun hsum (x, y)⟩
  have hlinear (x : ℝ) : L x = (x : ℂ) * L 1 := by
    simpa [A, Algebra.smul_def] using map_real_smul A L.continuous x (1 : ℝ)
  refine ⟨L 1, ?_, ?_⟩
  · intro t
    obtain ⟨x, rfl⟩ := E.surjective t
    rw [hpow, ← hlinear, hLift]
  · intro z hz
    apply exp_real_mul_injective
    intro x
    rw [← hpow, ← hz, ← hlinear, hLift]

/-- A unitary character of the positive reals is a power with purely imaginary exponent. -/
theorem existsUnique_unitaryComplexPower (c : ℝ≥0ˣ →ₜ* ℂ) (hc : ∀ t, ‖c t‖ = 1) :
    ∃! z : ℂ, z.re = 0 ∧ ∀ t : ℝ≥0ˣ, c t = (valℝ t : ℂ) ^ z := by
  obtain ⟨z, hz, huniq⟩ := existsUnique_complexPower c
  refine ⟨z, ⟨?_, hz⟩, fun a ha ↦ huniq a ha.2⟩
  let t := Units.mk0 (2 : ℝ≥0) (by norm_num)
  have h := hc t
  rw [hz t, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t))] at h
  apply (Real.rpow_right_inj (x := 2) (by norm_num) (by norm_num)).mp
  change (2 : ℝ) ^ z.re = 1 at h
  simpa using h

/-- A unitary character of the real units is uniquely specified by an imaginary exponent
of the absolute value and a parity on the sign. -/
theorem existsUnique_realUnits_character_parameters (c : ℝˣ →ₜ* ℂ) (hc : ∀ x, ‖c x‖ = 1) :
    ∃! a : ℂ × Fin 2, a.1.re = 0 ∧ ∀ x : ℝˣ, c x =
      (‖(x : ℝ)‖ : ℂ) ^ a.1 * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.2.val := by
  classical
  let i : ℝ≥0ˣ →ₜ* ℝˣ := ⟨Units.map NNReal.toRealHom.toMonoidHom,
    NNReal.continuous_coe.units_map _⟩
  obtain ⟨z, ⟨hz₀, hz⟩, huniq⟩ := existsUnique_unitaryComplexPower (c.comp i) (fun t ↦ hc (i t))
  let k : Fin 2 := if c (-1) = 1 then 0 else 1
  have hk : c (-1) = (-1 : ℂ) ^ k.val := by
    have hsq : c (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
    rcases sq_eq_one_iff.mp hsq with h | h
    · norm_num [k, h]
    · norm_num [k, h]
  refine ⟨(z, k), ⟨hz₀, ?_⟩, ?_⟩
  · intro x
    let t := Units.map nnNormHom.toMonoidHom x
    have hp : c (i t) = (‖(x : ℝ)‖ : ℂ) ^ z := hz t
    by_cases hx : 0 < (x : ℝ)
    · have he : i t = x := Units.ext (abs_of_pos hx)
      simpa [hx, he] using hp
    · have he : x = i t * (-1) := by
        apply Units.ext
        change (x : ℝ) = |(x : ℝ)| * (-1)
        rw [abs_of_nonpos (le_of_not_gt hx)]
        ring
      rw [ite_eq_right hx]
      change c x = (‖(x : ℝ)‖ : ℂ) ^ z * (-1 : ℂ) ^ k.val
      exact (congrArg c he).trans ((map_mul c _ _).trans (congrArg₂ (· * ·) hp hk))
  · rintro ⟨a, b⟩ ⟨ha₀, hab⟩
    apply Prod.ext
    · apply huniq a
      refine ⟨ha₀, fun t ↦ ?_⟩
      have hpos : 0 < (i t : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
      change c (i t) = ((i t : ℝ) : ℂ) ^ a
      simpa [ite_eq_left hpos, Real.norm_eq_abs, abs_of_pos hpos] using hab (i t)
    · have hneg : c (-1) = (-1 : ℂ) ^ b.val := by
        have h := hab (-1)
        norm_num at h
        exact h
      have hinj : Function.Injective (fun j : Fin 2 ↦ (-1 : ℂ) ^ j.val) := by
        intro j l h
        fin_cases j <;> fin_cases l <;> norm_num at *
      exact hinj (hneg.symm.trans hk)

end RiemannMasullo
