module

public import Mathlib.NumberTheory.NumberField.HeckeLFunction
public import RiemannMasullo.ForMathlib.NumberTheory.ArithmeticFunction.LFunction
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
import Mathlib.RingTheory.PowerSeries.WellKnown

public section

open Filter Function ArithmeticFunction NumberField IsDedekindDomain

namespace RiemannMasullo

open Classical in
/-- The inverse Euler polynomial has geometric coefficients, with ratio zero at ramified places. -/
theorem hecke_localPowerSeries_eq_mk {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (χ : HeckeCharacter R F) (v : HeightOneSpectrum R) :
    let a := if χ.IsUnramifiedAt v then χ.localValue v else 0
    χ.localPowerSeries v = PowerSeries.mk (fun k ↦ a ^ k) := by
  classical
  let a := if χ.IsUnramifiedAt v then χ.localValue v else 0
  let P : PowerSeries ℂ := 1 - PowerSeries.C a * PowerSeries.X
  have hP : (χ.localPolynomial v : PowerSeries ℂ) = P := by
    by_cases h : χ.IsUnramifiedAt v <;> simp [HeckeCharacter.localPolynomial, a, P, h]
  have hinv : P * χ.localPowerSeries v = 1 := by
    rw [HeckeCharacter.localPowerSeries, hP]
    apply PowerSeries.mul_invOfUnit
    simp [P]
  have hgeom : PowerSeries.mk (fun k ↦ a ^ k) * P = 1 := by
    simpa [P, PowerSeries.rescale_mk, PowerSeries.rescale_X] using
      congrArg (PowerSeries.rescale a) (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  exact (left_inv_eq_right_inv hgeom hinv).symm

/-- Finite products of a Hecke character's local factors stabilize at each Dirichlet
coefficient. Here the cardinality in Mathlib's Euler factor equals the absolute ideal norm. -/
theorem heckeLocalEulerFactor_eventually_prod_eq {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter (𝓞 F) F) (n : ℕ) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in atTop, (∏ v ∈ S, χ.localEulerFactor v) n =
      χ.LFunction n := by
  simpa only [HeckeCharacter.LFunction, HeckeCharacter.localEulerFactor,
    card_residueField_adicCompletion] using
    tendsTo_eulerProduct_ofPowerSeries (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal.absNorm)
      χ.localPowerSeries (fun v ↦ by simp [HeckeCharacter.localPowerSeries,
        PowerSeries.constantCoeff_invOfUnit]) n

/-- A local character value of norm at most one gives an absolutely convergent geometric
Dirichlet series. Its sum of absolute terms is at most exp(2 N(v)^(-Re(s))). -/
theorem LSeries_heckeLocalEulerFactor_bound {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 < s.re)
    (hχ : χ.IsUnramifiedAt v → ‖χ.localValue v‖ ≤ 1) :
    LSeriesSummable (χ.localEulerFactor v) s ∧
      (∑' n, ‖LSeries.term (χ.localEulerFactor v) s n‖) ≤
        Real.exp (2 * (v.asIdeal.absNorm : ℝ) ^ (-s.re)) := by
  classical
  let q := v.asIdeal.absNorm
  let a := if χ.IsUnramifiedAt v then χ.localValue v else 0
  have hq : 1 < q := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hq' : 0 < (q : ℝ) := by linarith
  let r := (q : ℝ) ^ (-s.re)
  have hr : 0 ≤ r := Real.rpow_nonneg hq'.le _
  have hrhalf : r ≤ 1 / 2 := calc
    r ≤ (q : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ (q : ℝ)) (by linarith)
    _ = 1 / q := by rw [Real.rpow_neg hq'.le, Real.rpow_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq₂
  have ha : ‖a‖ ≤ 1 := by
    dsimp [a]
    split_ifs with h
    · exact hχ h
    · simp
  let z := a * (q : ℂ) ^ (-s)
  have hz : ‖z‖ ≤ r := by
    change ‖a * ((q : ℝ) : ℂ) ^ (-s)‖ ≤ r
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq' _, Complex.neg_re]
    exact mul_le_of_le_one_left hr ha
  have hz' : ‖z‖ < 1 := by linarith
  have hsum : HasSum (fun n ↦ ‖LSeries.term (χ.localEulerFactor v) s n‖) (1 - ‖z‖)⁻¹ := by
    rw [HeckeCharacter.localEulerFactor, card_residueField_adicCompletion, hecke_localPowerSeries_eq_mk]
    exact hasSum_norm_LSeries_term_ofPowerSeries hq hz'
  refine ⟨hsum.summable.of_norm, hsum.tsum_eq.le.trans ?_⟩
  apply le_trans (b := 2 * r + 1) _ (Real.add_one_le_exp _)
  rw [inv_eq_one_div, div_le_iff₀ (sub_pos.mpr hz')]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - 2 * r) hr,
    mul_le_mul_of_nonneg_left hz (by linarith : 0 ≤ 2 * r + 1)]

/-- The formal Hecke Euler product defines an absolutely convergent Dirichlet series to the
right of one if all its unramified local values have norm at most one. -/
theorem LSeriesSummable_heckeLFunction {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter (𝓞 F) F) {s : ℂ} (hs : 1 < s.re)
    (hχ : ∀ v, χ.IsUnramifiedAt v → ‖χ.localValue v‖ ≤ 1) : LSeriesSummable χ.LFunction s := by
  have hq : Summable fun v : HeightOneSpectrum (𝓞 F) ↦ (v.asIdeal.absNorm : ℝ) ^ (-s.re) :=
    (summable_absNorm_rpow F hs).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hlocal (v) := LSeries_heckeLocalEulerFactor_bound χ v hs (hχ v)
  exact LSeriesSummable_of_eventuallyEq_finset_prod _ _ s (hq.mul_left 2)
    (fun v ↦ mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (fun v ↦ (hlocal v).1) (fun v ↦ (hlocal v).2)
    (heckeLocalEulerFactor_eventually_prod_eq χ)

end RiemannMasullo
