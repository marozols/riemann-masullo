module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero

import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec1

/-!
# Printed completion and indexing claims in §10.4.3

The corresponding quotient and kernel declarations are in `Sec4b.lean`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 3

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "C₁[" F "]" => (ideleClassNorm F).ker
local notation "m[" F "]" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C[F] →ₜ* ℝ≥0ˣ)
local notation "μ[" F "]" => ideleClassTamagawaMeasure F
local notation "logNorm[" F "]" => fun g : C[F] ↦ Real.log ((ideleClassNorm F g).val : ℝ)
local notation "E[" F ", " ω "]" =>
  ↥(modulatedDecayIsotype m[F] univ (mem_univ (0 : ℝ)) ω)
local notation "W[" F ", " s "]" =>
  CompactIntervalSobolev μ[F] logNorm[F] 0 0 s
local notation "θ(" ω ", " f ")" => (homogeneousAdelicTheta ω (f).val : _ → ℂ)
local notation "thetaClosure(" F ", " ω ", " a ", " s ")" =>
  closure {v : W[F, s] | ∃ f : adelePolarSubspace F,
    (v : C[F] → ℂ) =ᵐ[μ[F]] modulationWeight m[F] a (θ(ω, f))}

/-- Paper: Diagram (10.4.3.2), p. 465. As printed: bare norm completion
induces the lower right quotient arrow. On representatives, an untwisted
polar-free theta function completes to a vector in the closure of the
twisted theta image. The diagram note in `Sec4b.lean` inserts the twist
before completion (ERRATA F193). -/
def Printed.spectralLineCompletion_descends : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ω : PontryaginDual C₁[F]) (a s : ℝ), 0 ≤ s →
    ∀ (u : E[F, ω]) (v : W[F, s]),
      (v : C[F] → ℂ) =ᵐ[μ[F]] u.val.val →
      (∃ f : adelePolarSubspace F, u.val.val = θ(ω, f)) →
      v ∈ thetaClosure(F, ω, a, s)

section CompletionCounterexample

local notation "C" => C[ℚ]
local notation "K" => C₁[ℚ]
local notation "m" => m[ℚ]
local notation "μC" => μ[ℚ]
local notation "μ₁" => normOneIdeleClassTamagawaMeasure ℚ
local notation "B" => SchwartzBruhat (Multiplicative (AdeleRing (𝓞 ℚ) ℚ))
local notation "c(" z ")" => ideleClassNormTwist (1 : PontryaginDual C) z
local notation "θ₁(" f ")" => (homogeneousAdelicTheta (1 : PontryaginDual K) f : C → ℂ)
local notation "ΛG" => gaussianCompletedHeckeL (1 : PontryaginDual C)
local notation "ΛC" => continuedCompletedHeckeL (1 : PontryaginDual C)

-- This is the norm-section argument used in the injectivity of the trivial twist
-- chart in Chapter 3, §2.
private theorem ratUnitaryTwist_injective : Injective
    (ideleClassNormTwist (1 : PontryaginDual C)) := by
  intro z w he
  let τ (u : ℝ≥0ˣ) : C := QuotientGroup.mk (canonicalIdeleNormSection ℚ u)
  have hτ (u : ℝ≥0ˣ) : ideleClassNorm ℚ (τ u) = u :=
    canonicalIdeleNormSection_rightInverse ℚ u
  let d := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 z
  refine (existsUnique_complexPower d).unique (fun _ ↦ one_mul _) fun u ↦ ?_
  have h := DFunLike.congr_fun he (τ u)
  change 1 * (((ideleClassNorm ℚ (τ u)).val : ℝ) : ℂ) ^ z =
    1 * (((ideleClassNorm ℚ (τ u)).val : ℝ) : ℂ) ^ w at h
  rw [hτ, one_mul, one_mul] at h
  exact (one_mul _).trans h

private theorem ratUnitaryTwist_regular {z : ℂ} (hz : z ≠ 0) (hz₁ : z ≠ 1) :
    c(z) ≠ 1 ∧ c(z) ≠ c(1) := by
  refine ⟨fun h ↦ hz (ratUnitaryTwist_injective (h.trans ?_)),
    fun h ↦ hz₁ (ratUnitaryTwist_injective h)⟩
  ext g
  change (1 : ℂ) = 1 * (((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ (0 : ℂ)
  simp

private theorem gaussianRat_eq_continued : ΛG = ΛC := by
  funext z
  have hG := globalIdelicZFunction_meromorphic (adelicStandardGaussian (1 : PontryaginDual C)) 1
  have hC := (continuedCompletedHeckeL_spec (1 : PontryaginDual C)).1
  have he := meromorphicContinuation_eventuallyEq hG.meromorphicOn hC.meromorphicOn (fun s hs ↦ by
    change ΛG s = ΛC s
    rw [gaussianCompletedHeckeL_eq_completedHeckeL (1 : PontryaginDual C) s hs,
      (continuedCompletedHeckeL_spec (1 : PontryaginDual C)).2 ⟨s, hs⟩]
    norm_num [NumberField.discr_rat]) z
  exact (((hG (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hC (mem_univ z))).mp he).eq_of_nhds

private theorem gaussianRat_nonzero_imag (t : ℝ) (ht : 0 < t) :
    ΛG ((t : ℂ) * Complex.I) ≠ 0 := by
  let w := (t : ℂ) * Complex.I
  let z := 1 - w
  have hz : z.re = 1 := by simp [z, w, Complex.mul_re]
  have hzne : z ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [z, w, Complex.mul_im] at him
    linarith
  have hz₀ : z ≠ 0 := fun h ↦ by simp [h] at hz
  let hC := continuedCompletedHeckeL_spec (1 : PontryaginDual C)
  have hau : AnalyticAt ℂ ΛG z :=
    (globalIdelicZFunction_poles (adelicStandardGaussian (1 : PontryaginDual C)) 1).1
      z (ratUnitaryTwist_regular hz₀ hzne)
  have hzN : ΛC z ≠ 0 := by
    intro hzero
    have ha : AnalyticAt ℂ ΛC z := gaussianRat_eq_continued ▸ hau
    have htO : 0 < meromorphicOrderAt ΛC z := by
      rw [ha.meromorphicOrderAt_eq]
      have hne := ha.analyticOrderAt_ne_zero.mpr hzero
      cases horder : analyticOrderAt ΛC z using ENat.recTopCoe with
      | top => simp
      | coe n => simpa [horder, Nat.pos_iff_ne_zero] using hne
    have hbad := completedHeckeL_continuation_zeros (1 : PontryaginDual C) ΛC hC.1 hC.2
      (hz ▸ zero_lt_one) htO
    exact (lt_irrefl (1 : ℝ)) (hz ▸ hbad)
  have hdual : ∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), ΛC s =
      completedHeckeL ((1 : PontryaginDual C)⁻¹) s := by
    simpa only [inv_one] using hC.2
  obtain ⟨ε, -, -, hfun⟩ := completedHeckeL_continuation_functionalEquation
    (1 : PontryaginDual C) ΛC ΛC hC.1 hC.2 hC.1 hdual
  rw [gaussianRat_eq_continued]
  intro hzero
  have hzero' : ΛC w = 0 := hzero
  exact hzN ((hfun w).trans (by rw [hzero', mul_zero]))

private theorem fourierZero_translate (u : IdeleGroup (𝓞 ℚ) ℚ) (f : B) :
    adeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd 0) =
      (((ideleNorm ℚ u).val : ℝ) : ℂ) * adeleSchwartzFourier f (Multiplicative.ofAdd 0) := by
  let q := (adelicThetaLinearMap ℚ).ker.mkQL
  let ρ := (existsUnique_globalThetaAction (F := ℚ)).exists.choose
  have hρ : ρ (QuotientGroup.mk u : C) (q f) = q (schwartzBruhatUnitTranslate u f) :=
    (existsUnique_globalThetaAction (F := ℚ)).exists.choose_spec.2 u f
  have h := globalThetaPolarValues_snd_translate (F := ℚ) (QuotientGroup.mk u) (q f)
  rw [hρ, globalThetaPolarValues_mk, globalThetaPolarValues_mk] at h
  exact h

private theorem exists_polar_eval_ne_zero (t : ℝ) (ht : 0 < t) :
    ∃ f : adelePolarSubspace ℚ, globalIdelicZFunction f.val c((t : ℂ) * Complex.I) ≠ 0 := by
  let z := (t : ℂ) * Complex.I
  have hz : z ≠ 0 := by simp [z, ht.ne']
  have hz₁ : z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at this
  have hreg := ratUnitaryTwist_regular hz hz₁
  obtain ⟨D, -, hD, hfac⟩ := adelicEigendistribution_normalized (1 : PontryaginDual C)
  let G : B := adelicStandardGaussian (1 : PontryaginDual C)
  have hd := (hD z (D z)).1 rfl
  have hnon : c(z) ≠ 1 := hreg.1
  obtain ⟨g, hg⟩ : ∃ g : C, c(z) g ≠ 1 := by
    by_contra! h
    exact hnon (ContinuousMonoidHom.ext h)
  have hqsurj : Surjective (QuotientGroup.mk : IdeleGroup (𝓞 ℚ) ℚ → C) := QuotientGroup.mk_surjective
  obtain ⟨u, rfl⟩ := hqsurj g
  let r : ℂ := (((ideleNorm ℚ u).val : ℝ) : ℂ)
  let q := c(z) (QuotientGroup.mk u)
  have hq : q ≠ 1 := hg
  have hqr : q ≠ r := by
    intro h
    have hnorm : ‖q‖ = 1 := by
      rw [norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm ℚ)
        (isProperMap_ideleClassNorm ℚ) (ideleClassNorm_ne_one (F := ℚ))]
      rw [quasiCharacterAbscissa_ideleClassNormTwist]
      simp [z, Complex.mul_re]
    have hr : (ideleNorm ℚ u).val = 1 := by
      rw [h] at hnorm
      change ‖((((ideleNorm ℚ u).val : ℝ≥0) : ℝ) : ℂ)‖ = 1 at hnorm
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)] at hnorm
      exact_mod_cast hnorm
    apply hq
    simpa [r, hr] using h
  let A := schwartzBruhatUnitTranslate u
  let d := A G - G
  let f := A d - r • d
  have hd₀ : d (Multiplicative.ofAdd 0) = 0 := by
    change A G (Multiplicative.ofAdd 0) - G (Multiplicative.ofAdd 0) = 0
    rw [schwartzBruhatUnitTranslate_apply, mul_zero, sub_self]
  have hf : f ∈ adelePolarSubspace ℚ := by
    apply (mem_adelePolarSubspace f).2
    refine ⟨?_, ?_⟩
    · change A d (Multiplicative.ofAdd 0) - r * d (Multiplicative.ofAdd 0) = 0
      rw [schwartzBruhatUnitTranslate_apply, mul_zero, hd₀, mul_zero, sub_self]
    · change (adelePolarValues f).2 = 0
      rw [show f = A d - r • d from rfl, map_sub, map_smul]
      change adeleSchwartzFourier (A d) (Multiplicative.ofAdd 0) -
        r * adeleSchwartzFourier d (Multiplicative.ofAdd 0) = 0
      rw [fourierZero_translate, sub_self]
  have htrans (k : B) : D z (A k) = q * D z k := hd.1 u k
  have hval : D z d = q - 1 := by
    change D z (A G - G) = _
    rw [map_sub, htrans, show D z G = 1 from hd.2, mul_one]
  have hval' : D z f = (q - r) * (q - 1) := by
    change D z (A d - r • d) = _
    rw [map_sub, map_smul, htrans, hval, smul_eq_mul, sub_mul]
  refine ⟨⟨f, hf⟩, ?_⟩
  change globalIdelicZFunction f c(z) ≠ 0
  rw [hfac z hreg.1 hreg.2 f, hval']
  exact mul_ne_zero (gaussianRat_nonzero_imag t ht)
    (mul_ne_zero (sub_ne_zero.mpr hqr) (sub_ne_zero.mpr hq))

local notation "E₀" => E[ℚ, (1 : PontryaginDual K)]
local notation "U" => ModulatedExponentialDecay m univ
local notation "hm" =>
  (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation m)
local notation "hsurj" => (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.2.2.2.1

/-- Lift the compact average to the decay space, as in the periodization proof
in Chapter 4, §5. -/
private theorem exists_ratHomogeneousTheta_decay (f : adelePolarSubspace ℚ) :
    ∃ u : E₀, u.val.val = θ₁(f.val) := by
  let : (μ₁).IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  let : (μ₁).Regular := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.2.1
  let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
  let : LocallyCompactSpace K :=
    (isCompact_iff_compactSpace.mpr ‹CompactSpace K›).isClosed.locallyCompactSpace
  let ψ : U := ⟨adelicTheta f.val, adelicTheta_mem_modulatedExponentialDecay_of_polar f.val f.property⟩
  obtain ⟨ρ, hρ, -⟩ := exists_modulatedExponentialDecay_translationAction m univ hm hsurj
    ordConnected_univ univ_nonempty
  let ω : PontryaginDual K := 1
  obtain ⟨A, hA, -⟩ := existsUnique_modulatedExponentialDecay_isotypicProjector m univ hm hsurj
    ordConnected_univ univ_nonempty μ₁ ρ hρ ω
  let zero : (Set.univ : Set ℝ) := ⟨0, mem_univ _⟩
  let v : U := (A ψ).val
  have htw (g : U) (x : C) : modulatedExponentialDecayTwist m univ zero g x = g.val x :=
    congrFun (modulationWeight_zero m g.val) x
  have hval (x : C) : v.val x = ((μ₁).real univ)⁻¹ • θ₁(f.val) x := by
    have he := congrArg (fun g : SchwartzBruhat C ↦ g x) (hA ψ zero)
    rw [htw] at he
    refine he.trans ((schwartzBruhatIsotypicProjector_apply m hm μ₁ ω
      (modulatedExponentialDecayTwist m univ zero ψ) x).2.trans ?_)
    congr 1
    change (∫ k : K, star (ω k : ℂ) *
      modulatedExponentialDecayTwist m univ zero ψ (k.val⁻¹ * x) ∂μ₁) = _
    simp only [htw, ω, PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul]
    have hev (k : K) : ψ.val (k.val⁻¹ * x) = adelicTheta f.val ((k⁻¹ : K).val * x) := rfl
    rw [integral_congr_ae (.of_forall hev)]
    have hInv := integral_inv_eq_self (fun k : K ↦ adelicTheta f.val (k.val * x)) μ₁
    rw [hInv]
    unfold homogeneousAdelicTheta
    simp only [ContinuousMap.coe_mk, PontryaginDual.one_apply, Circle.coe_one, mul_one]
  have hmass := (measureReal_univ_pos (μ := μ₁)).ne'
  let v' : U := ((μ₁).real univ : ℂ) • v
  have hrep : v'.val = θ₁(f.val) := by
    funext x
    change ((μ₁).real univ : ℂ) * v.val x = _
    rw [hval, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hmass), one_mul]
  refine ⟨⟨v', (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) _).mpr ?_⟩, hrep⟩
  intro k x
  rw [hrep]
  exact homogeneousAdelicTheta_homogeneous ω f.val k x

/-- The unnormalized norm-one average multiplies a Mellin integral in the trivial
component by the mass of the compact norm-one group. -/
private theorem ratHomogeneousTheta_mellin (f : adelePolarSubspace ℚ) (z : ℂ) :
    (∫ g, θ₁(f.val) g * c(z) g ∂μC) =
      ((μ₁).real univ : ℂ) * globalIdelicZFunction f.val c(z) := by
  let : (μC).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  let : (μ₁).IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
  obtain ⟨hf₀, hfF⟩ := (mem_adelePolarSubspace f.val).mp f.property
  let v : C → ℂ := fun g ↦ adelicTheta f.val g * c(z) g
  have hv : Integrable v μC := globalThetaMellinIntegral_integrable_of_vanishing f.val hf₀ hfF c(z)
  have hcv : Continuous v := (adelicTheta f.val).continuous.mul (c(z)).continuous
  have hc (k : K) : c(z) k.val = 1 := by
    change 1 * (((ideleClassNorm ℚ k.val).val : ℝ) : ℂ) ^ z = 1
    rw [show ideleClassNorm ℚ k.val = 1 from k.property]
    simp
  have hnorm (k : K) : Integrable (fun g : C ↦ v (k.val * g)) μC :=
    (measurePreserving_mul_left μC k.val).integrable_comp_of_integrable hv
  have hprod : Integrable (fun p : K × C ↦ v (p.1.val * p.2)) ((μ₁).prod μC) := by
    apply (integrable_prod_iff (hcv.comp ((continuous_subtype_val.comp continuous_fst).mul
      continuous_snd)).aestronglyMeasurable).mpr
    refine ⟨.of_forall hnorm, ?_⟩
    have hin (k : K) : (∫ g : C, ‖v (k.val * g)‖ ∂μC) = ∫ g, ‖v g‖ ∂μC :=
      integral_mul_left_eq_self (μ := μC) (fun g ↦ ‖v g‖) k.val
    exact (integrable_const _).congr (.of_forall fun k ↦ (hin k).symm)
  have haverage (g : C) : θ₁(f.val) g * c(z) g = ∫ k : K, v (k.val * g) ∂μ₁ := by
    unfold homogeneousAdelicTheta
    rw [ContinuousMap.coe_mk, ← integral_mul_const]
    refine integral_congr_ae (.of_forall fun k ↦ ?_)
    simp only [PontryaginDual.one_apply, Circle.coe_one, mul_one, one_mul, v, map_mul, hc]
  simp_rw [haverage]
  rw [← integral_integral_swap hprod]
  simp_rw [integral_mul_left_eq_self (μ := μC) v]
  rw [integral_const, Complex.real_smul]
  exact congrArg (((μ₁).real univ : ℂ) * ·)
    (congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf₀ hfF) c(z))

private theorem exists_ratLineRepresentative (u : E₀) :
    ∃ v : W[ℚ, 2], (v : C → ℂ) =ᵐ[μC] u.val.val := by
  let action := exists_modulatedExponentialDecay_translationAction m univ hm hsurj
    ordConnected_univ univ_nonempty
  let ω : PontryaginDual K := 1
  let S := actionIsotype (action.choose.comp (ideleClassNorm ℚ).ker.subtype) ω
  have hu : u.val ∈ S := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    apply Subtype.ext
    funext x
    exact (action.choose_spec.1 k.val u.val x).trans
      ((mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) _).mp u.property k x)
  let φ : S := ⟨u.val, hu⟩
  obtain ⟨i, hi, -⟩ := existsUnique_spectralLineTestCompletion (F := ℚ) 0
    (show (0 : ℝ) ≤ 2 by norm_num) ω
  exact ⟨(i φ).val, (hi.1 φ).trans (.of_eq (modulationWeight_zero m u.val.val))⟩

local notation "shift(" a ", " t ")" => (((a : ℝ) : ℂ) + (t : ℂ) * Complex.I)

private theorem ratNormTwist_modulationWeight (a : ℝ) (z : ℂ) (v : C → ℂ) (g : C) :
    modulationWeight m a v g * c(z) g = v g * c((a : ℂ) + z) g := by
  let x : ℝ := (ideleClassNorm ℚ g).val
  have hx : 0 < x := NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g))
  change ((x ^ a : ℝ) : ℂ) * v g * (1 * (x : ℂ) ^ z) =
    v g * (1 * (x : ℂ) ^ ((a : ℂ) + z))
  rw [Complex.ofReal_cpow hx.le, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  ring

private theorem exists_ratLineEvaluation (a t : ℝ)
    (hz : 0 < meromorphicOrderAt ΛC (shift(a, t))) :
    ∃ L₂ : StrongDual ℂ W[ℚ, 2], ∀ v : W[ℚ, 2],
      L₂ v = ∫ g, v g * c((t : ℂ) * Complex.I) g ∂μC := by
  let χ : PontryaginDual K → PontryaginDual C := fun _ ↦ 1
  let z := shift(a, t)
  obtain ⟨hL, hR⟩ := continuedCompletedHeckeL_spec (1 : PontryaginDual C)
  have ho₂ : meromorphicOrderAt ΛC 2 = 0 := by
    apply (hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr
    rw [show ΛC 2 = completedHeckeL (1 : PontryaginDual C) ⟨2, by norm_num⟩ from hR ⟨2, by norm_num⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos _ (by norm_num))
      (finiteHeckeL_ne_zero_of_one_lt_re _ _)
  have hf := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z) (by rw [ho₂]; simp)
  have hp : 0 < (meromorphicOrderAt ΛC z).untop₀ := by
    apply WithTop.coe_lt_coe.mp
    rwa [WithTop.coe_untop₀_of_ne_top hf]
  have hn : 0 < (meromorphicOrderAt ΛC z).untop₀.toNat := by omega
  let j : SpectralLineJetIndex χ a 2 := ⟨(1, t, 0), by
    rw [lt_spectralBoundaryMultiplicity]
    exact ⟨hn, by norm_num⟩⟩
  obtain ⟨L₂, hL₂, -⟩ := spectralLineJet_functional χ (by norm_num : (1 : ℝ) < 2) j
  refine ⟨L₂, fun v ↦ ?_⟩
  simpa only [j, χ, spectralZeroJet, pow_zero, mul_one, Complex.ofReal_zero, zero_add] using (hL₂ v).2

private theorem spectralLineCompletion_descends_false_of_zero (t : ℝ) (ht : 0 < t)
    (hz : 0 < meromorphicOrderAt ΛC (shift((1 / 2 : ℝ), t))) :
    ¬ Printed.spectralLineCompletion_descends := by
  intro hdesc
  let a : ℝ := 1 / 2
  let z := (t : ℂ) * Complex.I
  have hregular := ratUnitaryTwist_regular
    (z := shift(a, t)) (by
      intro h
      have := congrArg Complex.re h
      norm_num [a, Complex.mul_re] at this)
    (by
      intro h
      have := congrArg Complex.re h
      norm_num [a, Complex.mul_re] at this)
  obtain ⟨L₂, hL₂⟩ := exists_ratLineEvaluation a t hz
  obtain ⟨f, hf⟩ := exists_polar_eval_ne_zero t ht
  obtain ⟨u, hu⟩ := exists_ratHomogeneousTheta_decay f
  obtain ⟨v, hv⟩ := exists_ratLineRepresentative u
  have hvL : L₂ v ≠ 0 := by
    rw [hL₂ v]
    have he : (∫ g, v g * c(z) g ∂μC) = ∫ g, θ₁(f.val) g * c(z) g ∂μC :=
      integral_congr_ae ((hv.trans (.of_eq hu)).mono fun g hg ↦ congrArg (· * c(z) g) hg)
    rw [he, ratHomogeneousTheta_mellin]
    let : (μ₁).IsHaarMeasure :=
      (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
    let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ₁)).ne') hf
  have hG : ΛG (shift(a, t)) = 0 := by
    rw [gaussianRat_eq_continued]
    by_contra hn
    have ho := ((continuedCompletedHeckeL_spec (1 : PontryaginDual C)).1
      (mem_univ (shift(a, t)))).meromorphicOrderAt_eq_zero_iff.mpr hn
    exact (lt_irrefl 0) (ho ▸ hz)
  obtain ⟨D, -, -, hD⟩ := adelicEigendistribution_normalized (1 : PontryaginDual C)
  have hsubset : {w : W[ℚ, 2] | ∃ f' : adelePolarSubspace ℚ,
      (w : C → ℂ) =ᵐ[μC] modulationWeight m a (θ₁(f'.val))} ⊆ {w | L₂ w = 0} := by
    rintro w ⟨f', hw⟩
    change L₂ w = 0
    rw [hL₂ w]
    have he : (∫ g, w g * c(z) g ∂μC) =
        ∫ g, θ₁(f'.val) g * c(shift(a, t)) g ∂μC := by
      apply integral_congr_ae
      filter_upwards [hw] with g hg
      rw [hg]
      exact ratNormTwist_modulationWeight a z _ _
    rw [he, ratHomogeneousTheta_mellin, hD _ hregular.1 hregular.2 f'.val, hG, zero_mul, mul_zero]
  exact hvL (closure_minimal hsubset (isClosed_eq L₂.continuous continuous_const)
    (hdesc ℚ 1 a 2 (by norm_num) u v hv ⟨f, hu⟩))

/-- The positive ordinate is supplied by Thomas Lince's vendored Hardy first-zero
certificate. Chapter 13 compares the finite trivial Hecke L-function with Riemann zeta,
and its archimedean factor is nonvanishing on this half-plane. -/
private theorem exists_ratLinePositiveZero :
    ∃ t : ℝ, 0 < t ∧ 0 < meromorphicOrderAt ΛC (shift((1 / 2 : ℝ), t)) := by
  obtain ⟨t, ht, hzeta⟩ := HardyFirstZero.first_zero_on_line
  refine ⟨t, by linarith [ht.1], ?_⟩
  let z := shift((1 / 2 : ℝ), t)
  have hz : z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at this
  have ha := analyticOn_riemannZeta _ hz
  have hmer : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have he := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C)
    hmer (fun s ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property])
    (s := z) (by norm_num [z, Complex.mul_re])
  have hz₀ : riemannZeta z = 0 := by simpa [z] using hzeta
  change 0 < meromorphicOrderAt ΛC z
  rw [← he, ha.meromorphicOrderAt_eq]
  have hne := ha.analyticOrderAt_ne_zero.mpr hz₀
  cases ho : analyticOrderAt riemannZeta z using ENat.recTopCoe with
  | top => simp
  | coe k => simpa [ho, Nat.pos_iff_ne_zero] using hne

/-- Paper: Diagram (10.4.3.2), p. 465. Over `ℚ` in the trivial isotype, take
a positive critical-line zeta ordinate. Two norm translations of the standard
adelic Gaussian cancel its polar values while preserving a nonzero Mellin value
at the corresponding frequency on the imaginary axis. The Mellin functional is
continuous in the Sobolev norm of degree two. It vanishes on the twisted theta
closure by the forward factorization at the critical-line zero. -/
theorem Printed.spectralLineCompletion_descends_false :
    ¬ Printed.spectralLineCompletion_descends := by
  obtain ⟨t, ht, hz⟩ := exists_ratLinePositiveZero
  exact spectralLineCompletion_descends_false_of_zero t ht hz

end CompletionCounterexample

/-- Paper: Diagram (10.4.3.2), p. 465. As printed: the lower right arrow
induced by bare completion is injective. On representatives, if the
completed vector belongs to the twisted theta closure, the source
representative is already an untwisted polar-free theta function.
The diagram note in `Sec4b.lean` identifies the needed closure condition.
`spectralLineKernel_orthogonalLift` uses the completed quotient (ERRATA F194). -/
def Printed.spectralLineCompletion_quotientInjective : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ω : PontryaginDual C₁[F]) (a s : ℝ), 0 ≤ s →
    ∀ (u : E[F, ω]) (v : W[F, s]),
      (v : C[F] → ℂ) =ᵐ[μ[F]] u.val.val →
      v ∈ thetaClosure(F, ω, a, s) →
      ∃ f : adelePolarSubspace F, u.val.val = θ(ω, f)

/-- Norm weights compose by addition of their exponents. -/
private theorem spectralLineCompletion_comp_weight {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (m : G →ₜ* ℝ≥0ˣ) (a b : ℝ) (f : G → ℂ) :
    modulationWeight m a (modulationWeight m b f) = modulationWeight m (a + b) f := by
  funext x
  change ((_ : ℝ) : ℂ) * (((_ : ℝ) : ℂ) * f x) = ((_ : ℝ) : ℂ) * f x
  rw [Real.rpow_add (NNReal.coe_pos.mpr (Units.zero_lt _)), Complex.ofReal_mul, mul_assoc]

/-- Twisting preserves the all-exponent decay space and its norm-one isotype. -/
private theorem spectralLineCompletion_weight_isotype {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (ω : PontryaginDual m.toMonoidHom.ker) (a : ℝ)
    (u : modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) :
    ∃ w : modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω,
      w.val.val = modulationWeight m a u.val.val := by
  let f := modulationWeight m a u.val.val
  have hf : f ∈ modulatedExponentialDecaySubmodule m univ := by
    simp only [modulatedExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap]
    intro b
    change modulationWeight m b.val (modulationWeight m a u.val.val) ∈ _
    rw [spectralLineCompletion_comp_weight]
    exact modulationWeight_mem_schwartzBruhat m univ ⟨b.val + a, trivial⟩ u.val
  let y : ModulatedExponentialDecay m univ := ⟨f, hf⟩
  refine ⟨⟨y, (mem_modulatedDecayIsotype_iff m ω _ _ y).mpr ?_⟩, rfl⟩
  intro k x
  have hu := (mem_modulatedDecayIsotype_iff m ω _ _ u.val).mp u.property k x
  change ((_ : ℝ) : ℂ) * u.val.val (k.val⁻¹ * x) =
    (ω k : ℂ) * (((_ : ℝ) : ℂ) * u.val.val x)
  have hk : m k.val = 1 := k.property
  simp only [map_mul, map_inv, hk, inv_one, one_mul, hu, mul_left_comm]

/-- At degree zero the Sobolev measure is Haar measure, so every Schwartz–Bruhat
function has an almost-everywhere equal representative in this completion. -/
private theorem spectralLineCompletion_zero_sobolev {F : Type} [Field F] [NumberField F]
    (f : SchwartzBruhat C[F]) : ∃ v : W[F, 0], (v : C[F] → ℂ) =ᵐ[μ[F]] f.val := by
  let _ : (μ[F]).IsHaarMeasure := instIdeleClassHaarMeasureSec1
  have hμ : (μ[F]).withDensity (fun g : C[F] ↦ ENNReal.ofReal
      (intervalSobolevDensity 0 0 0 (Real.log ((ideleClassNorm F g).val : ℝ)))) = μ[F] := by
    simp [intervalSobolevDensity]
  have rep (ν : Measure C[F]) (hν : ν = μ[F]) :
      ∃ v : Lp ℂ 2 ν, (v : C[F] → ℂ) =ᵐ[μ[F]] f.val := by
    subst ν
    have h := schwartzBruhat_memLp_two_of_integrable f (SchwartzBruhat.integrable μ[F] f)
    exact ⟨h.toLp f.val, h.coeFn_toLp⟩
  exact rep _ hμ

/-- Apply the purported injectivity at the opposite weight and Sobolev degree zero
to recover an untwisted theta representative. Twisting it back gives descent. -/
private theorem spectralLineCompletion_descends_of_quotientInjective
    (hinj : Printed.spectralLineCompletion_quotientInjective) :
    Printed.spectralLineCompletion_descends := by
  rintro F _ _ ω a s hs u v hv ⟨f, hf⟩
  obtain ⟨w, hw⟩ := spectralLineCompletion_weight_isotype m[F] ω (-a) u
  let ψ := modulatedExponentialDecayTwist m[F] univ ⟨0, trivial⟩ w.val
  have hψ : ψ.val = w.val.val := modulationWeight_zero m[F] w.val.val
  obtain ⟨v', hv'⟩ := spectralLineCompletion_zero_sobolev ψ
  rw [hψ] at hv'
  have hmem : v' ∈ thetaClosure(F, ω, -a, 0) :=
    subset_closure ⟨f, by simpa only [hw, hf] using hv'⟩
  obtain ⟨g, hg⟩ := hinj F ω (-a) 0 le_rfl w v' hv' hmem
  apply subset_closure
  refine ⟨g, ?_⟩
  rw [← hg, hw, spectralLineCompletion_comp_weight, add_neg_cancel, modulationWeight_zero]
  exact hv

/-- Paper: Diagram (10.4.3.2), p. 465. Take `F = ℚ`, the trivial isotype,
`a = 2` and `s = 4`. The polar-free test with real factor
`G − 3G(2 ·) + 2G(4 ·)` for `G(x) = exp(−πx²)` and integral finite
indicator has twisted theta with nowhere-zero Fourier transform in log norm.
Its translates span a dense subspace of the completed trivial isotype.
For a zeta zero with ordinate `γ > 0`, use a nonzero nonnegative smooth
log-norm bump supported in `|x| < π/(4γ)`. Its Mellin value has positive
real part there. It represents a nonzero source class and its completion
is in the twisted theta closure. -/
theorem Printed.spectralLineCompletion_quotientInjective_false :
    ¬ Printed.spectralLineCompletion_quotientInjective := by
  exact fun h ↦ Printed.spectralLineCompletion_descends_false
    (spectralLineCompletion_descends_of_quotientInjective h)

local notation "zeroOrder(" χ ", " a ", " t ")" =>
  meromorphicOrderAt (continuedCompletedHeckeL χ) ((a : ℂ) + (t : ℂ) * Complex.I)
local notation "lineZeros(" χ ", " a ")" =>
  {t : ℝ // 0 < zeroOrder(χ, a, t)}
local notation "lineJetIndices(" χ ", " ω ", " t ", " a ", " s ")" =>
  {i : ℕ × ℕ × ℕ // i.2.2 <
    min (zeroOrder((χ) ((ω) i.1), a, ((t) i.1 i.2.1).val)).untop₀.toNat
      ⌊(s - 1) / 2 + 1⌋₊}

/-- Paper: Theorem 10.4.3.1, enumeration clause (2), p. 466. As printed:
each base character has an enumeration indexed by all nonnegative integers
of its zero ordinates on the line of real part a, ordered by absolute value.
The zero indexing of `spectralLineQuotientKernel_tendsto` allows finite
and empty rows (ERRATA F197). -/
def Printed.spectralLineZeroEnumeration : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a : ℝ), 0 < a →
    ∀ (χ : PontryaginDual C₁[F] → PontryaginDual C[F]),
      IsSpectralBasepointChoice χ → ∀ ω,
        ∃ t : ℕ ≃ lineZeros(χ ω, a), Monotone (fun j ↦ |(t j).val|)

/-- Paper: Theorem 10.4.3.1, enumeration clause (2), p. 466. For `F = ℚ`
choose the trivial extension of the trivial norm-one character and set
`a = 2`. The completed zeta function has no zeros on this line, so the
enumeration cannot give a value even at index zero. -/
theorem Printed.spectralLineZeroEnumeration_false :
    ¬ Printed.spectralLineZeroEnumeration := by
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let ω : PontryaginDual C₁[ℚ] := 1
  obtain ⟨e, _⟩ := hall ℚ 2 (by norm_num) χ hχ ω
  let t := e 0
  let z : ℂ := 2 + (t.val : ℂ) * Complex.I
  have hz : 1 < z.re := by norm_num [z]
  have hval : continuedCompletedHeckeL (χ ω) z ≠ 0 := by
    rw [show continuedCompletedHeckeL (χ ω) z = completedHeckeL (χ ω) ⟨z, hz⟩ from
      (continuedCompletedHeckeL_spec (χ ω)).2 ⟨z, hz⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos (χ ω) (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re (χ ω) ⟨z, hz⟩)
  have horder := ((continuedCompletedHeckeL_spec (χ ω)).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval
  have ht : 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) z := t.property
  exact (not_lt_of_ge horder.le) ht

/-- Paper: Theorem 10.4.3.5, enumeration clauses (2)–(3), p. 472. As printed:
the ordered enumeration of strip zero pairs has an entry for every natural
number. The indexing in `spectralStripQuotientKernel_tendsto` uses just
the existing strip zeros (ERRATA F197).
Deviation: Clause (2) omits the offset range. Read it on the domain of
(10.4.3.38) in clause (3), the boundary and interior of the strip. -/
def Printed.spectralStripZeroEnumeration : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α : ℝ), 0 < a → 0 ≤ α →
    ∀ (χ : PontryaginDual C₁[F] → PontryaginDual C[F]),
      IsSpectralBasepointChoice χ → ∀ ω,
        ∃ z : ℕ ≃ {p : ℝ × ℝ // p.2 ∈ Icc (-α) α ∧ 0 < zeroOrder(χ ω, a + p.2, p.1)},
          Monotone (fun j ↦ |(z j).val.1|)

/-- Paper: Theorem 10.4.3.5, enumeration clauses (2)–(3), p. 472. For
`F = ℚ` and the trivial basepoint take `a = 2` and `α = 0`.
Formula (10.4.3.38) forces the offset at index zero to be zero, so this
entry would be a completed zeta zero on the zero-free line of real part 2. -/
theorem Printed.spectralStripZeroEnumeration_false :
    ¬ Printed.spectralStripZeroEnumeration := by
  intro hall
  apply Printed.spectralLineZeroEnumeration_false
  intro F _ _ a ha χ hχ ω
  obtain ⟨z, hz⟩ := hall F a 0 ha le_rfl χ hχ ω
  let Z := {p : ℝ × ℝ // p.2 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < zeroOrder(χ ω, a + p.2, p.1)}
  have hzero (p : Z) : p.val.2 = 0 := by simpa using p.property.1
  let e : Z ≃ lineZeros(χ ω, a) :=
    { toFun := fun p ↦ ⟨p.val.1, by simpa only [hzero p, Complex.ofReal_zero, add_zero] using p.property.2⟩
      invFun := fun t ↦ ⟨(t.val, 0), by simp, by simpa only [Complex.ofReal_zero, add_zero] using t.property⟩
      left_inv := fun p ↦ Subtype.ext (Prod.ext rfl (hzero p).symm)
      right_inv := fun _ ↦ rfl }
  exact ⟨z.trans e, hz⟩

/-- Paper: Theorem 10.4.3.1(2), pp. 467–468. As printed: for a sequence in
the jet index set (10.4.3.11), escaping to the point of the one-point
compactification of the discrete index set is equivalent to both zero
coordinates tending to infinity. The rectangles in
`spectralKernelRectangle` already have the product order on their
endpoints (ERRATA F198). -/
def Printed.spectralLineJet_cofinite_iff_coordinates : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → 1 < s →
    ∀ (χ : PontryaginDual C₁[F] → PontryaginDual C[F]), IsSpectralBasepointChoice χ →
      ∀ (ω : ℕ ≃ PontryaginDual C₁[F])
        (t : ∀ k : ℕ, ℕ ≃ lineZeros(χ (ω k), a)),
        (∀ k, Monotone (fun j ↦ |(t k j).val|)) →
        ∀ i : ℕ → lineJetIndices(χ, ω, t, a, s),
          Tendsto i atTop cofinite ↔
            Tendsto (fun n ↦ ((i n).val.1, (i n).val.2.1)) atTop atTop

/-- The dual of the rational norm-one group is countably infinite. Single-place sign
changes give distinct involutions in the norm kernel. -/
private theorem spectralLineJet_rational_characters :
    Nonempty (ℕ ≃ PontryaginDual C₁[ℚ]) := by
  classical
  let V := IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)
  let U := (v : V) → (v.adicCompletionIntegers ℚ)ˣ
  obtain ⟨e, _⟩ := ratIdeleClassGroup_decomposition
  let sign (v : V) : U := Pi.mulSingle v (-1)
  have square (v : V) : e (1, sign v) ^ 2 = 1 := by
    rw [← map_pow, ← e.map_one]
    refine congrArg e (Prod.ext (one_pow _) ?_)
    funext w
    by_cases h : w = v
    · subst w
      simp [sign]
    · simp [sign, Pi.mulSingle_eq_of_ne h]
  let g (v : V) : C₁[ℚ] := ⟨e (1, sign v), by
    change ideleClassNorm ℚ (e (1, sign v)) = 1
    apply sq_eq_one.mp
    rw [← map_pow, square, map_one]⟩
  have hinj : Injective g := by
    intro v w heq
    by_contra h
    have hu := congrArg (fun p : ℝ≥0ˣ × U ↦ p.2 v)
      (e.injective (congrArg Subtype.val heq))
    have hfalse : (-1 : (v.adicCompletionIntegers ℚ)ˣ) = 1 := by
      simpa [sign, Pi.mulSingle_eq_of_ne h] using hu
    have := congrArg (fun u : (v.adicCompletionIntegers ℚ)ˣ ↦ (u.val : v.adicCompletion ℚ)) hfalse
    have badK : (-1 : v.adicCompletion ℚ) = 1 := by simpa using this
    have bad : (-1 : ℚ) = 1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective
      (by simpa only [map_neg, map_one] using badK)
    norm_num at bad
  let _ : Infinite V := Infinite.of_injective
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
  let _ : Infinite C₁[ℚ] := Infinite.of_injective g hinj
  let _ : CompactSpace C₁[ℚ] := isCompact_iff_compactSpace.mp
    ((isProperMap_ideleClassNorm ℚ).isCompact_preimage (isCompact_singleton (x := 1)))
  let _ : LocallyCompactSpace C₁[ℚ] := inferInstance
  let _ : SecondCountableTopology C₁[ℚ] := Topology.IsInducing.subtypeVal.secondCountableTopology
  let _ : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let _ : SecondCountableTopology (PontryaginDual C₁[ℚ]) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁[ℚ] Circle).secondCountableTopology
  let _ : Countable (PontryaginDual C₁[ℚ]) := countable_of_Lindelof_of_discrete
  let _ : Infinite (PontryaginDual C₁[ℚ]) := by
    apply not_finite_iff_infinite.mp
    intro hfin
    obtain ⟨d, _⟩ := pontryaginDual_bidual (G := C₁[ℚ])
    exact (Finite.of_injective d d.injective).false
  exact nonempty_equiv_of_countable

/-- Bauer's critical-line theorem for primitive Dirichlet characters gives infinitely
many ordinates for each rational unitary Hecke character. An imaginary norm twist
translates the ordinates. See Bauer, *Zeros of Dirichlet L-series on the critical
line*, Corollary 1, p. 38. -/
private theorem spectralLineJet_rational_criticalLine_infinite (χ : PontryaginDual C[ℚ]) :
    Infinite (lineZeros(χ, (1 / 2 : ℝ))) := by sorry

/-- The order of the completed Hecke function is finite everywhere, since its order
is finite at 2. -/
private theorem spectralLineJet_order_ne_top {F : Type} [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (z : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) z ≠ ⊤ := by
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z)
  intro h
  have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) 2 :=
    h ▸ WithTop.coe_lt_top (0 : ℤ)
  have hb := completedHeckeL_continuation_zeros χ _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
  norm_num at hb

/-- Only finitely many ordinates in a row have bounded absolute value. Their complex
points belong to the divisor support on a compact vertical segment. -/
private theorem spectralLineJet_bounded_ordinates {F : Type} [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (a R : ℝ) :
    {t : lineZeros(χ, a) | |t.val| ≤ R}.Finite := by
  let z (y : ℝ) : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  let K := z '' Icc (-R) R
  have hc : IsCompact K := isCompact_Icc.image (by fun_prop : Continuous z)
  let f := continuedCompletedHeckeL χ
  have hf : MeromorphicOn f K := fun z _ ↦ (continuedCompletedHeckeL_spec χ).1.meromorphicOn z (mem_univ z)
  have hinj : Injective (fun t : lineZeros(χ, a) ↦ z t.val) := by
    intro x y h
    exact Subtype.ext (by simpa [z] using congrArg Complex.im h)
  apply (((MeromorphicOn.divisor f K).finiteSupport hc).preimage hinj.injOn).subset
  intro t ht
  have htK : z t.val ∈ K := ⟨t.val, abs_le.mp ht, rfl⟩
  change MeromorphicOn.divisor f K (z t.val) ≠ 0
  rw [hf.divisor_apply htK, Ne, WithTop.untop₀_eq_zero]
  exact not_or.mpr ⟨t.property.ne', spectralLineJet_order_ne_top χ _⟩

/-- Rank the ordinates by absolute value, breaking ties by signed value. Every
initial segment is finite, so the ranks form an infinite subset of the naturals. -/
private theorem spectralLineJet_ordered_ordinates {F : Type} [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (a : ℝ) [Infinite (lineZeros(χ, a))] :
    ∃ e : ℕ ≃ lineZeros(χ, a), Monotone (fun j ↦ |(e j).val|) := by
  classical
  let Z := lineZeros(χ, a)
  let key (t : Z) := toLex (|t.val|, t.val)
  let pred (t : Z) := {u : Z | key u < key t}
  let rank (t : Z) := (pred t).ncard
  have hlt {u t : Z} (h : key u < key t) : rank u < rank t := by
    refine Set.ncard_lt_ncard ?_ ?_
    · refine Set.ssubset_iff_subset_ne.mpr ⟨fun x hx ↦ lt_trans hx h, fun heq ↦ ?_⟩
      have hu : u ∈ pred t := h
      rw [← heq] at hu
      exact lt_irrefl (key u) hu
    · exact (spectralLineJet_bounded_ordinates χ a |t.val|).subset
        fun x hx ↦ Prod.Lex.monotone_fst (key x) (key t) (le_of_lt hx)
  have hinj : Injective rank := by
    intro u t h
    rcases lt_trichotomy (key u) (key t) with he | he | he
    · exact ((hlt he).ne h).elim
    · exact Subtype.ext (congrArg (fun p ↦ (ofLex p).2) he)
    · exact ((hlt he).ne h.symm).elim
  let r := Equiv.ofInjective rank hinj
  let _ : Infinite (range rank) := Infinite.of_injective r r.injective
  let n := Nat.Subtype.orderIsoOfNat (range rank)
  let e := n.toEquiv.trans r.symm
  refine ⟨e, fun i j hij ↦ ?_⟩
  have hle : rank (e i) ≤ rank (e j) := by
    change (r (r.symm (n i))).val ≤ (r (r.symm (n j))).val
    simpa only [Equiv.apply_symm_apply] using (show (n i).val ≤ (n j).val from n.monotone hij)
  exact Prod.Lex.monotone_fst _ _ (le_of_not_gt fun h ↦ (not_lt_of_ge hle) (hlt h))

/-- Paper: Theorem 10.4.3.1(2), pp. 467–468. Over ℚ take `a = 1/2` and
`s = 4`. Use the Dirichlet characters for the basepoints and put the
trivial character first. Every primitive Dirichlet row has infinitely many
critical-line ordinates (Bauer, Corollary 1), finitely many in each bounded
interval, so each admits an absolute-value enumeration. The zeroth jets
`(0,j,0)` escape each finite set while their first coordinate is constant. -/
theorem Printed.spectralLineJet_cofinite_iff_coordinates_false :
    ¬ Printed.spectralLineJet_cofinite_iff_coordinates := by
  classical
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨ω⟩ := spectralLineJet_rational_characters
  let a : ℝ := 1 / 2
  have rows (k : ℕ) : ∃ e : ℕ ≃ lineZeros(χ (ω k), a), Monotone (fun j ↦ |(e j).val|) := by
    let _ := spectralLineJet_rational_criticalLine_infinite (χ (ω k))
    exact spectralLineJet_ordered_ordinates _ _
  choose t ht using rows
  let J := lineJetIndices(χ, ω, t, a, (4 : ℝ))
  have hpos (n : ℕ) : 0 < (zeroOrder(χ (ω 0), a, (t 0 n).val)).untop₀.toNat := by
    have h := (t 0 n).property
    rw [← WithTop.coe_untop₀_of_ne_top (spectralLineJet_order_ne_top _ _)] at h
    have hh := WithTop.coe_lt_coe.mp h
    omega
  let row (n : ℕ) : J := ⟨(0, n, 0), lt_min (hpos n) (Nat.floor_pos.mpr (by norm_num))⟩
  have hinj : Injective row := fun m n h ↦ congrArg (fun x : J ↦ x.val.2.1) h
  have hesc : Tendsto row atTop cofinite := Nat.cofinite_eq_atTop ▸ hinj.tendsto_cofinite
  have hprod := (hall ℚ a 4 (by norm_num [a]) (by norm_num) χ hχ ω t ht row).mp hesc
  obtain ⟨n, hn⟩ := (hprod.eventually (eventually_ge_atTop (1, 0))).exists
  exact Nat.not_succ_le_zero 0 hn.1

/-- Paper: (10.4.3.21), p. 469. As printed: a finite rectangle has image
given by the finite sum over an initial segment of the lexicographic jet
order. This records the finiteness of the stated summation domain for every
endpoint. The kernel `spectralKernelRectangle` sums over the two coordinate
bounds (ERRATA F198). -/
def Printed.spectralLineJet_lexInitialSegment_finite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → 1 < s →
    ∀ (χ : PontryaginDual C₁[F] → PontryaginDual C[F]), IsSpectralBasepointChoice χ →
      ∀ (ω : ℕ ≃ PontryaginDual C₁[F])
        (t : ∀ k : ℕ, ℕ ≃ lineZeros(χ (ω k), a)),
        (∀ k, Monotone (fun j ↦ |(t k j).val|)) →
        ∀ i₀ : lineJetIndices(χ, ω, t, a, s),
          {i : lineJetIndices(χ, ω, t, a, s) | i = i₀ ∨
            Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) i.val i₀.val}.Finite

/-- Paper: (10.4.3.21), p. 469. Over ℚ take `a = 1/2`, `s = 4` and
the enumeration of Dirichlet rows with the trivial character first.
The lexicographic initial segment through `(1,0,0)` includes every
zeroth jet `(0,j,0)` of the trivial row. -/
theorem Printed.spectralLineJet_lexInitialSegment_finite_false :
    ¬ Printed.spectralLineJet_lexInitialSegment_finite := by
  classical
  intro hfin
  apply Printed.spectralLineJet_cofinite_iff_coordinates_false
  intro F _ _ a s ha hs χ hχ ω t ht i
  let J := lineJetIndices(χ, ω, t, a, s)
  have hcut : 0 < ⌊(s - 1) / 2 + 1⌋₊ := Nat.floor_pos.mpr (by linarith)
  have ordpos (k n : ℕ) : 0 < (zeroOrder(χ (ω k), a, ((t k) n).val)).untop₀.toNat := by
    let z : ℂ := (a : ℂ) + (((t k) n).val : ℂ) * Complex.I
    let L := continuedCompletedHeckeL (χ (ω k))
    obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec (χ (ω k))
    have htwo : meromorphicOrderAt L 2 ≠ ⊤ := by
      intro h
      have hp : 0 < meromorphicOrderAt L 2 := h ▸ WithTop.coe_lt_top (0 : ℤ)
      have hb := completedHeckeL_continuation_zeros (χ (ω k)) _ hL heq
        (by norm_num : 0 < (2 : ℂ).re) hp
      norm_num at hb
    have hne : meromorphicOrderAt L z ≠ ⊤ := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ _) (mem_univ z) htwo
    have hp : 0 < meromorphicOrderAt L z := ((t k) n).property
    rw [← WithTop.coe_untop₀_of_ne_top hne] at hp
    have hint : 0 < (meromorphicOrderAt L z).untop₀ := WithTop.coe_lt_coe.mp hp
    change 0 < (meromorphicOrderAt L z).untop₀.toNat
    omega
  let j (k n : ℕ) : J := ⟨(k, n, 0), lt_min (ordpos k n) hcut⟩
  have hinj : Injective (j 0) := fun m n he ↦ congrArg (fun v : J ↦ v.val.2.1) he
  have hf := hfin F a s ha hs χ hχ ω t ht (j 1 0)
  apply False.elim
  apply (Set.infinite_range_of_injective hinj)
  apply hf.subset
  rintro _ ⟨n, rfl⟩
  exact Or.inr (Prod.Lex.left _ _ (Nat.zero_lt_succ 0))

end RiemannMasullo
