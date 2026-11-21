module

public import RiemannMasullo.Ch02_AdelicTheta.Sec3
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import RiemannMasullo.ForMathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Small-norm estimates for S-local adelic theta

Masullo, §2.4, pp. 106–116. As in §2.3, the Lean place set records the
finite places only. All archimedean places are included in `SAdeleRing`.
-/

@[expose] public noncomputable section

open Asymptotics Bornology Filter IsDedekindDomain MeasureTheory NumberField Topology
open scoped NNReal

namespace RiemannMasullo

variable (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "classOf" => (QuotientGroup.mk : Iₛ → SIdeleQuotient F S)
local notation "normℝ[" K "," V "]" =>
  fun (g : (SAdeleRing K V)ˣ) ↦ ((Units.val (sIdeleNorm K V g) : ℝ≥0) : ℝ)
local notation "smallNorm[" K "," V "]" => comap normℝ[K, V] (𝓝[>] (0 : ℝ))

-- As in §2.3, the homogeneous operator takes its Haar measure as a parameter.
local instance : MeasurableSpace J₁ := borel _

/-! ## The rational number field -/

section Rat

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- Paper: Proposition 2.4.1.1, p. 107. Over the rationals the theta
function grows at most as the absolute log norm to the number of finite
places in S, uniformly as the S-idelic norm tends to zero from above. -/
theorem sLocalAdelicTheta_rat_log_growth (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    (fun g ↦ sLocalAdelicTheta ℚ S f g) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (normℝ[ℚ, S] g)| ^ S.card) := by sorry

/-- Paper: Proposition 2.4.1.1, pp. 107, 110. Over the rationals the same
logarithmic growth bound holds for homogeneous theta for each continuous
character of the norm-one S-idele classes.
Deviation: As in §2.3, the Haar measure on those classes is explicit. -/
theorem sLocalHomogeneousAdelicTheta_rat_log_growth
    (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm ℚ S))) [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual ↥(MonoidHom.ker (sIdeleQuotientNorm ℚ S)))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    (fun g ↦ sLocalHomogeneousAdelicTheta ℚ S μ ω f (QuotientGroup.mk g)) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (normℝ[ℚ, S] g)| ^ S.card) := by sorry

end Rat

-- TODO(paper-gap): Lemma 2.4.1.2 prints C in (2.4.1.3) after quantifying Cφ.
-- A coefficient depending only on T, M, N and the bases fails for
-- M = 1, N = 2, a₁ = 2, T = 1 and φ(t) = K on (0, 1), zero for t ≥ 1.
-- At t = 2⁻ⁿ the sum is K n, so the coefficient must be at least K / log 2.

/-- A bounded function with power decay has a single majorant for all decay exponents
between zero and one. -/
private theorem geometric_grid_decay_majorant {N : ℕ} (hN : 1 ≤ N) {φ : ℝ → ℂ}
    {C A T : ℝ} (hC : 0 < C) (hb : ∀ y, 0 < y → ‖φ y‖ ≤ C)
    (hd : ∀ y, T ≤ y → ‖φ y‖ ≤ A * (y ^ N)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ y, 0 < y → ∀ L : ℝ, 1 ≤ L →
      ‖φ y‖ ≤ D * Real.exp (-Real.log y / L) := by
  let D := max (C * max 1 T) A
  have hCD : C ≤ D :=
    (le_mul_of_one_le_right hC.le (le_max_left 1 T)).trans (le_max_left _ _)
  refine ⟨D, hC.trans_le hCD, ?_⟩
  intro y hy L hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rcases le_total y 1 with hy₁ | hy₁
  · have hlog := Real.log_nonpos hy.le hy₁
    exact ((hb y hy).trans hCD).trans (le_mul_of_one_le_right (hC.le.trans hCD)
      (Real.one_le_exp (div_nonneg (neg_nonneg.mpr hlog) hL0.le)))
  · have hlinear : ‖φ y‖ * y ≤ D := by
      by_cases hT : T ≤ y
      · have hpow : y ≤ y ^ N := by simpa using pow_le_pow_right₀ hy₁ hN
        have hdec : ‖φ y‖ ≤ A / y ^ N := by simpa only [div_eq_mul_inv] using hd y hT
        exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans
          (((le_div_iff₀ (pow_pos hy N)).mp hdec).trans (le_max_right _ _))
      · exact (mul_le_mul (hb y hy) ((le_of_not_ge hT).trans (le_max_right _ _)) hy.le hC.le).trans
          (le_max_left _ _)
    calc
      ‖φ y‖ ≤ D * Real.exp (-Real.log y) := by
        rw [Real.exp_neg, Real.exp_log hy, ← div_eq_mul_inv]
        exact (le_div_iff₀ hy).mpr hlinear
      _ ≤ D * Real.exp (-Real.log y / L) := by
        gcongr
        apply (le_div_iff₀ hL0).mpr
        nlinarith [mul_nonneg (Real.log_nonneg hy₁) (sub_nonneg.mpr hL)]

/-- The mass of a geometric series with ratio exp(-b/L) is at most linear in L. -/
private theorem geometric_grid_factor_bound {b L : ℝ} (hb : 0 < b) (hL : 1 ≤ L) :
    (1 - Real.exp (-b / L))⁻¹ ≤ (1 + b⁻¹) * L := by
  have hL0 := zero_lt_one.trans_le hL
  let x := b / L
  have hx : 0 < x := div_pos hb hL0
  have hex : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  calc
    (1 - Real.exp (-b / L))⁻¹ = 1 + (Real.exp x - 1)⁻¹ := by
      rw [neg_div, Real.exp_neg]
      change (1 - (Real.exp x)⁻¹)⁻¹ = _
      field_simp [hex.ne', (Real.exp_pos x).ne']
      ring
    _ ≤ 1 + x⁻¹ := by
      gcongr
      linarith [Real.add_one_le_exp x]
    _ ≤ (1 + b⁻¹) * L := by
      dsimp [x]
      rw [inv_div, one_add_mul, div_eq_inv_mul]
      linarith

/-- Paper: Lemma 2.4.1.2, p. 107. For a bounded function with power decay
at infinity, the sum of the norms over the multiplicative grid with M bases
greater than one converges and is bounded by a constant times the Mth power
of the absolute log near zero.
Deviation: Equation (2.4.1.3) uses the existentially quantified constant
`Cφ`. The real-domain function is used only at positive arguments, and
summability is explicit. -/
theorem summable_geometric_grid_log_bound (M N : ℕ) (hM : 1 ≤ M) (hN : 1 < N)
    (a : Fin M → ℝ) (ha : ∀ i, 1 < a i) (φ : ℝ → ℂ)
    (hbounded : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ C)
    (hdecay : ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖φ t‖ ≤ A * (t ^ N)⁻¹) :
    ∃ T₀ Cφ : ℝ, 0 < T₀ ∧ 0 < Cφ ∧ ∀ t : ℝ, 0 < t → t < T₀ →
      let term : (Fin M → ℕ) → ℝ := fun k ↦ ‖φ ((∏ i, a i ^ k i) * t)‖
      Summable term ∧ (∑' k, term k) ≤ Cφ * |Real.log t| ^ M := by
  clear hM -- The product estimate also holds in dimension zero.
  obtain ⟨C, hC, hb⟩ := hbounded
  obtain ⟨A, T, -, -, hd⟩ := hdecay
  obtain ⟨D, hD, hmajor⟩ := geometric_grid_decay_majorant hN.le hC hb hd
  let b (i : Fin M) := Real.log (a i)
  have hbpos (i : Fin M) : 0 < b i := Real.log_pos (ha i)
  have hapos (i : Fin M) : 0 < a i := zero_lt_one.trans (ha i)
  let P := ∏ i, (1 + (b i)⁻¹)
  have hP : 0 < P := Finset.prod_pos fun i _ ↦ by have := hbpos i; positivity
  refine ⟨Real.exp (-1), D * Real.exp 1 * P, Real.exp_pos _, by positivity, ?_⟩
  intro t ht ht₀
  -- Choose the decay exponent 1/L so that the factor from t is exactly exp(1).
  let L := -Real.log t
  have hL : 1 ≤ L := by
    have h := (Real.log_lt_iff_lt_exp ht).mpr ht₀
    dsimp [L]
    linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let q (i : Fin M) := Real.exp (-b i / L)
  let w (k : Fin M → ℕ) := ∏ i, (q i) ^ k i
  have hq (i : Fin M) : q i < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr (hbpos i)) hL0)
  have hw : HasSum w (∏ i, (1 - q i)⁻¹) :=
    hasSum_prod_fin_of_nonneg (fun i n ↦ q i ^ n) _
      (fun i n ↦ pow_nonneg (Real.exp_nonneg _) _)
      (fun i ↦ hasSum_geometric_of_lt_one (Real.exp_nonneg _) (hq i))
  have hpoint (k : Fin M → ℕ) :
      ‖φ ((∏ i, a i ^ k i) * t)‖ ≤ D * Real.exp 1 * w k := by
    have hp : 0 < ∏ i, a i ^ k i := Finset.prod_pos fun i _ ↦ pow_pos (hapos i) _
    refine (hmajor _ (mul_pos hp ht) L hL).trans_eq ?_
    have hlog : -Real.log ((∏ i, a i ^ k i) * t) / L = 1 + ∑ i, (k i : ℝ) * (-b i / L) := by
      rw [Real.log_mul hp.ne' ht.ne', Real.log_prod (fun i _ ↦ (pow_pos (hapos i) _).ne')]
      simp only [Real.log_pow]
      have hterm (i : Fin M) : (k i : ℝ) * (-b i / L) = -((k i : ℝ) * b i) / L := by ring
      simp_rw [hterm]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib]
      change -((∑ i, (k i : ℝ) * b i) + Real.log t) / L = _
      have htL : Real.log t = -L := (neg_neg _).symm
      rw [htL]
      field_simp [hL0.ne']
      ring
    rw [hlog, Real.exp_add, Real.exp_sum, mul_assoc]
    simp only [Real.exp_nat_mul, w, q]
  have hsum := hw.mul_left (D * Real.exp 1)
  have hs := hsum.summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hpoint
  refine ⟨hs, (hs.tsum_le_tsum hpoint hsum.summable).trans ?_⟩
  rw [hsum.tsum_eq, abs_of_nonpos (by change Real.log t ≤ 0; dsimp [L] at hL; linarith)]
  change D * Real.exp 1 * (∏ i, (1 - q i)⁻¹) ≤ D * Real.exp 1 * P * L ^ M
  rw [mul_assoc (D * Real.exp 1)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD.le (Real.exp_nonneg _))
  calc
    (∏ i, (1 - q i)⁻¹) ≤ ∏ i, ((1 + (b i)⁻¹) * L) :=
      Finset.prod_le_prod₀ (fun i _ ↦ inv_nonneg.mpr (sub_nonneg.mpr (hq i).le))
        (fun i _ ↦ geometric_grid_factor_bound (hbpos i) hL)
    _ = P * L ^ M := by simp [P, Finset.prod_mul_distrib]

-- TODO(paper-gap): The geometric series in (2.4.1.5) has an unrounded
-- lower endpoint, and (2.4.1.8) loses a factor in the power of T. The
-- reduction in (2.4.1.14) changes the local support condition. The
-- application on p. 109 omits S = {∞}, where the S-units are {±1}.
-- TODO(paper-gap): The p. 110 ergodicity assertion fails for S = {∞, p} over ℚ.
-- On Hₚ with nonzero real coordinate, log |x| modulo log p is invariant.
-- Theta can be bounded at zero, for instance when S = {∞} over ℚ. Its
-- Mellin integral there fails to converge uniformly on the entire open
-- right half-plane, even for the real Gaussian with trivial character.

/-! ## The general case -/

local notation "normℝ" => normℝ[F, S]
local notation "smallNorm" => smallNorm[F, S]

-- TODO(paper-gap): In the proof of Theorem 2.4.2.1, (2.4.2.2) leaves x∞
-- free on the right after taking the supremum on the left. Equation
-- (2.4.2.3) fails for the real Gaussian times the local integer indicators
-- at 2 and 3. The count of S-unit multiples in a fixed real annulus
-- outside the ball can grow without bound. The averaged estimate
-- (2.4.2.4) alone does not give a pointwise bound.

/-- Paper: Theorem 2.4.2.1, p. 111. Below S-idelic norm one, the theta
function is bounded by a constant times the absolute log norm to the
power `|S| - 1`, plus an additive constant. Both constants are uniform
on a bounded set of Schwartz–Bruhat functions. -/
theorem sLocalAdelicTheta_log_growth_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖sLocalAdelicTheta F S f g‖ ≤
        C₁ * |Real.log (normℝ g)| ^ (Fintype.card (InfinitePlace F) + S.card - 1) + C₂ := by sorry

/-! ## Order of growth -/

variable (ε : ℝ) (hε : 0 < ε)

include hε

-- TODO(paper-gap): The derivative of φ(t, g) on p. 113 drops g and ω(g).
-- In (2.4.3.3) the supremum is unweighted since |g′| = 1. It can be
-- infinite, as for the Gaussian example at (2.4.2.3).

/-- Paper: Proposition 2.4.3.1(1), p. 113. Multiplying S-local theta by
any positive real power of the S-idelic norm gives a bounded function
as the norm tends to zero from above. -/
theorem sLocalAdelicTheta_norm_pow_isBigO (f : ℬₛ) :
    (fun g ↦ (normℝ g ^ ε) • sLocalAdelicTheta F S f g) =O[smallNorm]
      (fun _ : Iₛ ↦ (1 : ℝ)) := by sorry

/-- Paper: Proposition 2.4.3.1(1), p. 113. The same small-norm bound
holds for homogeneous theta multiplied by a positive norm power.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_isBigO
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁) (f : ℬₛ) :
    (fun g ↦ (normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)) =O[smallNorm]
      (fun _ : Iₛ ↦ (1 : ℝ)) := by sorry

/-- Paper: Proposition 2.4.3.1(2), p. 113. Below a positive norm cutoff
the bound for theta times a positive norm power is uniform on a bounded
set of test functions. -/
theorem sLocalAdelicTheta_norm_pow_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < T →
      ‖(normℝ g ^ ε) • sLocalAdelicTheta F S f g‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(2), p. 113. Below a positive norm cutoff
the corresponding homogeneous bound is uniform on a bounded set of test functions.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_bounded
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < T →
      ‖(normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(3), p. 113. The uniform bound for theta
times a positive norm power holds below S-idelic norm one. -/
theorem sLocalAdelicTheta_norm_pow_bounded_threshold_one
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖(normℝ g ^ ε) • sLocalAdelicTheta F S f g‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(3), p. 113. The corresponding uniform
homogeneous bound holds below S-idelic norm one.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_bounded_threshold_one
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖(normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C := by sorry

/-- Paper: Corollary 2.4.3.2, p. 115. Theta multiplied by any positive
real power of the S-idelic norm tends to zero as that norm tends to zero. -/
theorem sLocalAdelicTheta_norm_pow_tendsto_zero (f : ℬₛ) :
    Tendsto (fun g ↦ (normℝ g ^ ε) • sLocalAdelicTheta F S f g) smallNorm (𝓝 0) := by sorry

/-- Paper: Corollary 2.4.3.2, p. 115. The same vanishing holds for
homogeneous theta for every continuous character of the norm-one classes.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_tendsto_zero
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁) (f : ℬₛ) :
    Tendsto (fun g ↦ (normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g))
      smallNorm (𝓝 0) := by sorry

end RiemannMasullo
