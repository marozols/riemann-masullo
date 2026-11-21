module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Fourier coefficients of smooth unit-periodic functions -/

@[expose] public noncomputable section
open Function MeasureTheory Set Topology
open scoped ContDiff Real
namespace RiemannMasullo
local notation "T" => AddCircle (1 : ℝ)

/-- Every derivative of the pullback to the real line is one-periodic. -/
theorem unitCircle_periodic_iteratedDeriv (f : T → ℂ) (k : ℕ) :
    Periodic (iteratedDeriv k (fun x : ℝ ↦ f x)) 1 := by
  intro x
  have h : (fun y : ℝ ↦ f (↑(y + 1) : T)) = (fun y : ℝ ↦ f (↑y : T)) :=
    funext fun y ↦ by rw [AddCircle.coe_add_period]
  simpa only [h] using (congrFun (iteratedDeriv_comp_add_const k (fun y : ℝ ↦ f (↑y : T)) 1) x).symm

/-- The derivative of order k of a smooth circle function, as a continuous circle function. -/
def unitCircleJet (f : T → ℂ) (hf : ContDiff ℝ ∞ (fun x : ℝ ↦ f x)) (k : ℕ) : C(T, ℂ) where
  toFun := (unitCircle_periodic_iteratedDeriv f k).lift
  continuous_toFun := by
    apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
    simpa only [Function.comp_def, Periodic.lift_coe] using hf.continuous_iteratedDeriv k (by simp)

@[simp] theorem unitCircleJet_coe (f : T → ℂ) (hf : ContDiff ℝ ∞ (fun x : ℝ ↦ f x)) (k : ℕ) (x : ℝ) :
    unitCircleJet f hf k x = iteratedDeriv k (fun y : ℝ ↦ f y) x :=
  (unitCircle_periodic_iteratedDeriv f k).lift_coe x

private theorem unitCircle_fourierCoeffOn (f : T → ℂ) (n : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x : ℝ ↦ f x) n = fourierCoeff f n := by
  have he : AddCircle.liftIco 1 0 (fun x : ℝ ↦ f (↑x : T)) = f := by
    funext z
    let r := (AddCircle.equivIco (1 : ℝ) 0) z
    have hr : (r : ℝ) ∈ Ico 0 (0 + 1) := r.property
    have hcoe : ((r : ℝ) : T) = z := AddCircle.coe_equivIco
    rw [← hcoe, AddCircle.liftIco_coe_apply hr]
  have h := @fourierCoeff_liftIco_eq 1 inferInstance 0 (fun x : ℝ ↦ f (↑x : T)) n
  rw [he] at h
  simpa only [zero_add] using h.symm

/-- Differentiation multiplies the normalized Fourier coefficient by the circle frequency. -/
theorem unitCircleJet_fourierCoeff_succ (f : T → ℂ) (hf : ContDiff ℝ ∞ (fun x : ℝ ↦ f x))
    (k : ℕ) (n : ℤ) : fourierCoeff (unitCircleJet f hf (k + 1)) n =
      (2 * (Real.pi : ℂ) * Complex.I * n) * fourierCoeff (unitCircleJet f hf k) n := by
  let g (x : ℝ) := f (x : T)
  let D (j : ℕ) := iteratedDeriv j g
  have hder (x : ℝ) : HasDerivAt (D k) (D (k + 1) x) x := by
    rw [show D (k + 1) = deriv (D k) from iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k) x).hasDerivAt
  have hper : D k 1 = D k 0 := by simpa using unitCircle_periodic_iteratedDeriv f k 0
  have hcoeff (j : ℕ) : fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (D j) n =
      fourierCoeff (unitCircleJet f hf j) n := by
    simpa only [unitCircleJet_coe] using unitCircle_fourierCoeffOn (unitCircleJet f hf j) n
  rw [← hcoeff, ← hcoeff]
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, mul_zero, zero_mul]
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero, div_one, one_smul, neg_zero, fourier_zero, one_mul,
      smul_eq_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hder x)
      ((hf.continuous_iteratedDeriv (k+1) (by simp)).intervalIntegrable 0 1), hper, sub_self]
  · have h := fourierCoeffOn_of_hasDerivAt (show (0 : ℝ) < 1 by norm_num) hn (fun x _ ↦ hder x)
      ((hf.continuous_iteratedDeriv (k+1) (by simp)).intervalIntegrable 0 1)
    rw [hper, sub_self] at h
    simp only [mul_zero, Complex.ofReal_zero, sub_zero, Complex.ofReal_one, one_mul, zero_sub] at h
    rw [h]
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero, hn]

/-- The frequency multiplier for the m-th unit circle character. -/
def unitCircleFrequency (m : ℤ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I * m

/-- The Fourier coefficient of the k-th derivative carries the k-th power of the frequency. -/
theorem unitCircleJet_fourierCoeff (f : T → ℂ) (hf : ContDiff ℝ ∞ (fun x : ℝ ↦ f x))
    (k : ℕ) (m : ℤ) : fourierCoeff (unitCircleJet f hf k) m =
      unitCircleFrequency m ^ k * fourierCoeff f m := by
  induction k with
  | zero =>
    have h : (unitCircleJet f hf 0 : T → ℂ) = f := by
      funext z
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      simp
    simp [h]
  | succ k ih =>
    rw [unitCircleJet_fourierCoeff_succ, ih, pow_succ']
    simp [unitCircleFrequency, mul_assoc]

/-- A summable envelope for the Fourier coefficients after taking two extra derivatives. -/
def unitCircleFourierWeight (m : ℤ) : ℝ :=
  (if m = 0 then 1 else 0) + 1 / (m : ℝ) ^ 2

/-- The two-derivative Fourier envelope is nonnegative at every integer. -/
theorem unitCircleFourierWeight_nonneg (m : ℤ) : 0 ≤ unitCircleFourierWeight m := by
  unfold unitCircleFourierWeight
  split_ifs <;> positivity

/-- The envelope is summable over the integer frequencies. -/
theorem summable_unitCircleFourierWeight : Summable unitCircleFourierWeight := by
  have h₀ : Summable fun m : ℤ ↦ (if m = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun m hm ↦ by simp [show m ≠ 0 by simpa using hm]
  exact h₀.add (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2))

private theorem norm_unitCircle_fourierCoeff_le (f : C(T, ℂ)) (m : ℤ) : ‖fourierCoeff f m‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := (AddCircle.haarAddCircle : Measure T))
    (f := fun z : T ↦ fourier (-m) z • f z)
    (ae_of_all _ fun z ↦ by simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using f.norm_coe_le_norm z)
  simpa only [fourierCoeff, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

/-- Two extra derivatives bound each Fourier coefficient by a summable multiple of
the uniform norms of the two derivatives. -/
theorem norm_unitCircleJet_fourierCoeff_le (f : T → ℂ) (hf : ContDiff ℝ ∞ (fun x : ℝ ↦ f x))
    (k : ℕ) (m : ℤ) : ‖fourierCoeff (unitCircleJet f hf k) m‖ ≤
      unitCircleFourierWeight m * (‖unitCircleJet f hf k‖ + ‖unitCircleJet f hf (k+2)‖) := by
  let D := unitCircleJet f hf
  by_cases hm : m = 0
  · subst m
    simpa [unitCircleFourierWeight] using (norm_unitCircle_fourierCoeff_le (D k) 0).trans
      (le_add_of_nonneg_right (norm_nonneg (D (k + 2))))
  have hfreq : |(m : ℝ)| ≤ ‖unitCircleFrequency m‖ := by
    simp only [unitCircleFrequency, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    nlinarith [abs_nonneg (m : ℝ), mul_nonneg (abs_nonneg (m : ℝ)) (show 0 ≤ 2 * Real.pi - 1 by linarith [Real.pi_gt_three])]
  have hh := norm_unitCircle_fourierCoeff_le (D (k+2)) m
  change ‖fourierCoeff (unitCircleJet f hf (k+2)) m‖ ≤ _ at hh
  rw [unitCircleJet_fourierCoeff_succ, unitCircleJet_fourierCoeff_succ] at hh
  change ‖unitCircleFrequency m * (unitCircleFrequency m * fourierCoeff (D k) m)‖ ≤ ‖D (k+2)‖ at hh
  have hmul : (m : ℝ)^2 * ‖fourierCoeff (D k) m‖ ≤ ‖D (k+2)‖ := by
    calc
      _ = |(m : ℝ)| * |(m : ℝ)| * ‖fourierCoeff (D k) m‖ := by rw [← sq_abs, pow_two]
      _ ≤ ‖unitCircleFrequency m‖ * ‖unitCircleFrequency m‖ * ‖fourierCoeff (D k) m‖ := by gcongr
      _ ≤ ‖D (k+2)‖ := by simpa only [norm_mul, mul_assoc] using hh
  have hpos : 0 < (m : ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast hm)
  simp only [unitCircleFourierWeight, hm, ↓reduceIte, zero_add, one_div, ← div_eq_inv_mul]
  apply (le_div_iff₀ hpos).2
  rw [mul_comm]
  exact hmul.trans (le_add_of_nonneg_left (norm_nonneg _))

/-- The differentiated Fourier series converges uniformly to the corresponding derivative. -/
theorem hasSum_unitCircleJet_fourier (f : T → ℂ) (hf : ContDiff ℝ ∞ (fun x : ℝ ↦ f x)) (k : ℕ) :
    HasSum (fun m : ℤ ↦ (unitCircleFrequency m ^ k * fourierCoeff f m) • fourier m)
      (unitCircleJet f hf k) := by
  have hs : Summable (fourierCoeff (unitCircleJet f hf k)) :=
    (summable_unitCircleFourierWeight.mul_right _).of_norm_bounded (norm_unitCircleJet_fourierCoeff_le f hf k)
  simpa only [unitCircleJet_fourierCoeff] using hasSum_fourier_series_of_summable hs

/-- The k-th real derivative of the m-th character is the character multiplied by its
frequency to the k-th power. -/
theorem iteratedDeriv_unitCircle_fourier (m : ℤ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ ↦ fourier m (y : T)) x = unitCircleFrequency m ^ k * fourier m (x : T) := by
  let c := unitCircleFrequency m
  let g (x : ℝ) := Complex.exp (c * (x : ℂ))
  have he : (fun y : ℝ ↦ fourier m (y : T)) = g := by
    funext y
    simp [g, c, unitCircleFrequency]
  change iteratedDeriv k (fun y : ℝ ↦ fourier m (y : T)) x = c ^ k * (fun y : ℝ ↦ fourier m (y : T)) x
  rw [he]
  have hder (y : ℝ) : HasDerivAt g (g y * c) y := by
    simpa [g] using ((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul c).cexp
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, funext ih, ((hder x).const_mul (c ^ k)).deriv, pow_succ]
    ring

end RiemannMasullo
