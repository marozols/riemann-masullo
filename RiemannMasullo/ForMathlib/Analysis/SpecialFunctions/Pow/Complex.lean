module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
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

end RiemannMasullo
