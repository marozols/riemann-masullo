module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Logic.Equiv.Nat

/-! # Further assertions in the proofs of §10.3 that are false as printed -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "orderAt(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "lineZeros(" χ ", " a ")" => {t : ℝ | 0 < orderAt(χ, shift(a, t))}
local notation "floorCut(" s ")" => Nat.floor ((s - 1) / 2 + 1)

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
As printed: the smallest interval containing the selected ordinates in each active character
can be enlarged at both ends by a common positive amount while still containing exactly
those zeros on the line. The finite selections are stated one character at a time.
See `spectralConvolutionFiniteSum` and ERRATA F178. -/
def Printed.spectralLineSelection_exists_isolatingInterval : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty),
      (K : Set ℝ) ⊆ lineZeros(χ ω, a) →
      ∃ ε : ℝ, 0 < ε ∧
        Icc (K.min' hK - ε) (K.max' hK + ε) ∩ lineZeros(χ ω, a) = (K : Set ℝ)

/-- Three ordered critical-line zeros of the ordinary Riemann zeta function suffice
for the interval counterexample. This is a finite consequence of Hardy's theorem. -/
private theorem spectralLineSelection_three_zeta_zeros :
    ∃ u v w : ℝ, u < v ∧ v < w ∧ riemannZeta (shift(1 / 2, u)) = 0 ∧
      riemannZeta (shift(1 / 2, v)) = 0 ∧ riemannZeta (shift(1 / 2, w)) = 0 := by
  sorry

/-- A critical-line zero of ordinary zeta has positive order for the completed
L-function of the trivial rational character. -/
private theorem spectralLineSelection_mem_lineZeros (t : ℝ)
    (ht : riemannZeta (shift(1 / 2, t)) = 0) :
    t ∈ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2) := by
  let z : ℂ := shift(1 / 2, t)
  have hre : z.re = 1 / 2 := by simp [z]
  have hne : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  change 0 < meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z
  rw [← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
    (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]
  apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
  change riemannZeta z = 0 at ht
  rw [← ht]
  exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
Use F = ℚ, the trivial base character and a = 1/2. Let K consist of the first and third
distinct positive critical-line zeta ordinates. The omitted second ordinate lies inside
the closed interval for every ε > 0. -/
theorem Printed.spectralLineSelection_exists_isolatingInterval_false :
    ¬ Printed.spectralLineSelection_exists_isolatingInterval := by
  classical
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let χ' := Function.update χ 1 (1 : PontryaginDual C𝔽(ℚ))
  have hχ' : IsSpectralBasepointChoice χ' := by
    intro ω
    by_cases h : ω = 1
    · subst ω
      rw [show χ' 1 = 1 from Function.update_self ..]
      rfl
    · simpa [χ', Function.update_of_ne h] using hχ ω
  obtain ⟨u, v, w, huv, hvw, hu, hv, hw⟩ := spectralLineSelection_three_zeta_zeros
  let K : Finset ℝ := {u, w}
  have huK : u ∈ K := by simp [K]
  have hwK : w ∈ K := by simp [K]
  have hzeros : (K : Set ℝ) ⊆ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2) := by
    intro t ht
    rcases (show t = u ∨ t = w by simpa [K] using ht) with rfl | rfl
    · exact spectralLineSelection_mem_lineZeros _ hu
    · exact spectralLineSelection_mem_lineZeros _ hw
  have htriv : χ' 1 = 1 := Function.update_self ..
  obtain ⟨ε, hε, hK⟩ := hall ℚ χ' hχ' (1 / 2) 1 K ⟨u, huK⟩ (by simpa only [htriv] using hzeros)
  rw [htriv] at hK
  have hvK : v ∈ (K : Set ℝ) := by
    rw [← hK]
    refine ⟨⟨?_, ?_⟩, spectralLineSelection_mem_lineZeros _ hv⟩
    · exact (sub_le_self _ hε.le).trans ((K.min'_le u huK).trans huv.le)
    · exact hvw.le.trans ((K.le_max' w hwK).trans (le_add_of_nonneg_right hε.le))
  simp [K, huv.ne', hvw.ne] at hvK

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
As printed: in each such interval the number of jets is at most the floor cutoff times the
logarithm of the greater of the absolute values of the endpoints. The count includes all
the orders below the truncated multiplicity of each zero in the interval.
See `spectralConvolutionFiniteSum` and ERRATA F180. -/
def Printed.spectralLineBand_jetCount_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty)
      (ε : ℝ), 0 < ε →
      let l := K.min' hK - ε
      let r := K.max' hK + ε
      Icc l r ∩ lineZeros(χ ω, a) = (K : Set ℝ) →
      ((∑ t ∈ K, min ((orderAt(χ ω, shift(a, t))).untop₀.toNat) floorCut(s) : ℕ) : ℝ) ≤
        (floorCut(s) : ℝ) * Real.log (max |l| |r|)

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
Use F = ℚ, the trivial base character, a = 1/2 and s = 2. Select every distinct positive
critical-line zeta ordinate at most T, for large T, and enlarge by an isolating ε < 1.
The floor cutoff is one. Riemann–von Mangoldt and the positive proportion of simple
critical-line zeros (Bui–Conrey–Young, Theorem 1.1) give ≫ T log T jets from the simple
zeros alone. The printed upper bound is O(log T). -/
theorem Printed.spectralLineBand_jetCount_le_false :
    ¬ Printed.spectralLineBand_jetCount_le := by sorry

section Plancherel

local instance instNormOneLocallyCompactSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : LocallyCompactSpace C₁(F) := by
  have hc : IsCompact ((ideleClassNorm F).ker : Set C𝔽(F)) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  exact hc.isClosed.locallyCompactSpace

local instance instNormOneHaarSec3SpectralProofPrinted (F : Type) [Field F] [NumberField F] :
    (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1

local instance instIdeleClassDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C𝔽(F)) := borel _

local instance instNormOneDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C₁(F)) := borel _

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
As printed: in the coordinates induced by the norm section τ, the full Plancherel measure
is the product of ordinary Lebesgue measure in x and the Plancherel measure of the norm-one subgroup.
This is the radial normalization used in the proof of `spectralLineConvolution_trace`
and `spectralStripConvolution_trace` in the paper. See ERRATA F182. -/
def Printed.spectralPlancherelMeasure_eq_radialVolume_prod : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F)),
      (∀ (x : ℝ) (ω : PontryaginDual C₁(F)) (r : ℝ≥0ˣ) (k : C₁(F)),
        e (Multiplicative.ofAdd x, ω) (τ r * k.val) =
          ω k * Circle.exp (x * Real.log (r.val : ℝ))) →
      ∀ (ν₁ : Measure (PontryaginDual C₁(F))) (ν : Measure (PontryaginDual C𝔽(F))),
        IsLCAPlancherelMeasure (normOneIdeleClassTamagawaMeasure F) ν₁ →
        IsLCAPlancherelMeasure (ideleClassTamagawaMeasure F) ν →
        (volume.prod ν₁).map (fun p : ℝ × PontryaginDual C₁(F) ↦
          e (Multiplicative.ofAdd p.1, p.2)) = ν

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
Take F = ℚ with its norm section and induced dual isomorphism. Use the Gaussian exp(−y²/2)
in y = log |g|, constant on the norm-one subgroup. With the kernel exp(ixy) its radial
transform is √(2π) exp(−x²/2). The printed measure makes its squared norm 2π times the
original squared norm, since the fixed norm-one Plancherel measure already accounts for
the compact factor. The radial Plancherel measure is dx/(2π). -/
theorem Printed.spectralPlancherelMeasure_eq_radialVolume_prod_false :
    ¬ Printed.spectralPlancherelMeasure_eq_radialVolume_prod := by sorry

end Plancherel

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
As printed: for each norm-one character and any numbering of its line-zero ordinates by
the natural numbers, the Fourier–Mellin samples of every test decay rapidly. This is the
claim for an infinite zero set. See `spectralLineConvolution_trace` and ERRATA F183. -/
def Printed.spectralLineSamples_rapid_for_any_numbering : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (φ : BruhatCompactSupport C𝔽(F)) (ω : PontryaginDual C₁(F))
      (e : ℕ ≃ lineZeros(χ ω, a)) (k : ℕ),
      Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k * ∫ g,
        φ.val g * ideleClassNormTwist (χ ω) (shift(0, (e n).val)) g
          ∂ideleClassTamagawaMeasure F) atTop (𝓝 0)

/-- A compact bump supported away from zero has an entire Mellin transform.
A single translate of this transform avoids zero on any countable set. -/
private theorem spectralLineSamples_mellin_shift (b : ContDiffBump (1 : ℝ))
    (hb : b.rOut = 1 / 2) (t : ℕ → ℝ) :
    ∃ c : ℂ, ∀ n, mellin (fun x : ℝ ↦ (b x : ℂ)) ((t n : ℂ) * Complex.I + c) ≠ 0 := by
  let B (x : ℝ) : ℂ := b x
  have hlow (x : ℝ) (hx : x ≤ 1 / 2) : b x = 0 := by
    apply b.zero_of_le_dist
    rw [hb, Real.dist_eq, abs_of_nonpos (by linarith : x - 1 ≤ 0)]
    linarith
  have htop : B =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    change (b x : ℂ) = 0
    rw [b.zero_of_le_dist, Complex.ofReal_zero]
    rw [hb, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ x - 1)]
    linarith
  have hbot : B =ᶠ[𝓝[>] 0] 0 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx
    change (b x : ℂ) = 0
    simp [hlow x hx.le]
  have hM : Differentiable ℂ (mellin B) := by
    intro z
    apply mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := z.re - 1)
      ((Complex.continuous_ofReal.comp b.continuous).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    · exact htop.isBigO.trans (Asymptotics.isBigO_zero _ _)
    · linarith
    · exact hbot.isBigO.trans (Asymptotics.isBigO_zero _ _)
    · linarith
  have hne : mellin B 1 ≠ 0 := by
    simp only [mellin, sub_self, Complex.cpow_zero, one_smul, B]
    rw [show (∫ x : ℝ in Ioi 0, (b x : ℂ)) = ((∫ x : ℝ in Ioi 0, b x : ℝ) : ℂ) from integral_ofReal]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun x hx ↦
      hlow x ((not_lt.mp hx).trans (by norm_num)))]
    exact Complex.ofReal_ne_zero.mpr (b.integral_pos (μ := volume)).ne'
  let Z := (mellin B) ⁻¹' ({0} : Set ℂ)
  have hZ : Z.Countable := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (compl_mem_codiscrete_iff.mp ((show AnalyticOnNhd ℂ (mellin B) univ from fun z _ ↦ hM.analyticAt z).preimage_zero_mem_codiscrete hne)).2
  let bad := ⋃ n, (fun c : ℂ ↦ (t n : ℂ) * Complex.I + c) ⁻¹' Z
  have hbad : bad.Countable := Set.countable_iUnion fun n ↦ hZ.preimage (add_right_injective _)
  obtain ⟨c, hc⟩ := (hbad.dense_compl ℂ).nonempty
  refine ⟨c, fun n hn ↦ hc (mem_iUnion.mpr ⟨n, ?_⟩)⟩
  exact hn

/-- Composition with a smooth scalar function preserves Bruhat smoothness in
each elementary quotient chart. -/
private theorem spectralLineSamples_smooth_comp {G : Type*} [CommGroup G] [TopologicalSpace G]
    {v : G → ℂ} (hv : IsBruhatSmooth v) {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsBruhatSmooth (fun x ↦ f (v x)) := by
  intro p
  obtain ⟨k, hk, hi, hd⟩ := hv p
  refine ⟨k, hk, fun h x ↦ congrArg f (hi h x), fun a ha ↦ ?_⟩
  obtain ⟨q, hq, hdiff⟩ := hd a ha
  exact ⟨fun y ↦ f (q y), fun x ↦ congrArg f (hq x),
    fun e z b ↦ (hf.of_le (by simp)).comp (hdiff e z b)⟩

/-- A compactly supported radial test can have all its Mellin samples at a
specified sequence of frequencies nonzero. -/
private theorem spectralLineSamples_nonvanishing (t : ℕ → ℝ) :
    ∃ φ : BruhatCompactSupport C𝔽(ℚ), ∀ n,
      (∫ g, φ.val g * ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
        (shift(0, t n)) g ∂ideleClassTamagawaMeasure ℚ) ≠ 0 := by
  let b : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  obtain ⟨c, hc⟩ := spectralLineSamples_mellin_shift b rfl t
  let f (x : ℝ) : ℂ := (x : ℂ) ^ c * (b x : ℂ)
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases h : 0 < x
    · have he : (fun y : ℝ ↦ (y : ℂ) ^ c) =ᶠ[𝓝 x]
          fun y ↦ Complex.exp ((Real.log y : ℂ) * c) := by
        filter_upwards [lt_mem_nhds h] with y hy
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.ofReal_log hy.le]
      apply ContDiffAt.mul _ (Complex.ofRealCLM.contDiff.comp b.contDiff).contDiffAt
      apply ContDiffAt.congr_of_eventuallyEq _ he
      exact Complex.contDiff_exp.contDiffAt.comp x
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr h.ne')).mul contDiffAt_const)
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      have he : ∀ᶠ y in 𝓝 x, y < 1 / 2 := gt_mem_nhds (by linarith)
      filter_upwards [he] with y hy
      have hy' : b y = 0 := b.zero_of_le_dist (by
        rw [Real.dist_eq, abs_of_nonpos (by linarith : y - 1 ≤ 0)]
        change (1 / 2 : ℝ) ≤ _
        linarith)
      simp [f, hy']
  let N (g : C𝔽(ℚ)) : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
  let χ : QuasiCharacter C𝔽(ℚ) :=
    { toFun := fun g ↦ (N g : ℂ)
      map_one' := by simp [N]
      map_mul' := fun x y ↦ by simp [N]
      continuous_toFun := Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)) }
  have hs : IsBruhatSmooth (fun g ↦ f (N g)) :=
    spectralLineSamples_smooth_comp (v := fun x ↦ χ x) (f := fun z ↦ f z.re)
      ((mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth (G := C𝔽(ℚ)) χ))
      (hfs.comp Complex.reCLM.contDiff)
  let e := (Nonneg.unitsHomeomorphPos ℝ).symm
  let K := Icc (⟨1 / 2, by norm_num⟩ : {x : ℝ // 0 < x}) ⟨3 / 2, by norm_num⟩
  have hK : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    change IsCompact (Subtype.val '' Icc (⟨1 / 2, by norm_num⟩ : Ioi (0 : ℝ)) ⟨3 / 2, by norm_num⟩)
    rw [image_subtype_val_Icc]
    exact isCompact_Icc
  have hcs : HasCompactSupport (fun g ↦ f (N g)) := by
    apply HasCompactSupport.intro ((isProperMap_ideleClassNorm ℚ).isCompact_preimage
      (hK.image e.continuous))
    intro g hg
    suffices hb : b (N g) = 0 by simp [f, hb]
    by_contra hn
    have hb := subset_tsupport _ hn
    rw [b.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hb
    change -(1 / 2 : ℝ) ≤ N g - 1 ∧ N g - 1 ≤ 1 / 2 at hb
    apply hg
    refine ⟨e.symm (ideleClassNorm ℚ g), ?_, e.apply_symm_apply _⟩
    change (1 / 2 : ℝ) ≤ N g ∧ N g ≤ 3 / 2
    constructor <;> linarith [hb.1, hb.2]
  let φ : BruhatCompactSupport C𝔽(ℚ) := ⟨_, (mem_bruhatSmoothSubmodule_iff _).2 hs, hcs⟩
  have hφ (g : C𝔽(ℚ)) : φ.val g = introTraceTest (1 : PontryaginDual C𝔽(ℚ)) f g := by
    simp [φ, introTraceTest, N]
  let ν := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hvol : (ν univ).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨NeZero.ne _, measure_ne_top _ _⟩
  refine ⟨φ, fun n ↦ ?_⟩
  rw [(introTraceTest_mellin 1 f φ hφ _).2]
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr hvol)
  change mellin (fun x : ℝ ↦ (x : ℂ) ^ c • (b x : ℂ)) (shift(0, t n)) ≠ 0
  rw [mellin_cpow_smul]
  simpa only [Complex.ofReal_zero, zero_add] using hc n

/-- A permutation of any sequence of nonzero samples can move some samples far
enough out that multiplication by the index no longer tends to zero. -/
private theorem spectralLineSamples_bad_numbering (v : ℕ → ℂ) (hv : ∀ n, v n ≠ 0) :
    ∃ σ : Equiv.Perm ℕ, ¬ Tendsto (fun n : ℕ ↦ (n : ℂ) * v (σ n)) atTop (𝓝 0) := by
  let k (j : ℕ) := ⌈‖v (Nat.pair j 0)‖⁻¹⌉₊
  let σ := Nat.pairEquiv.symm.trans
    ((Equiv.prodCongrRight fun j ↦ Equiv.swap (k j) 0).trans Nat.pairEquiv)
  refine ⟨σ, fun h ↦ ?_⟩
  obtain ⟨j, hj⟩ := Metric.tendsto_atTop.mp h 1 zero_lt_one
  let n := Nat.pair j (k j)
  have he : σ n = Nat.pair j 0 := by
    change σ (Nat.pairEquiv (j, k j)) = _
    simp [σ, Equiv.prodCongrRight_apply, Nat.pairEquiv_apply]
  have hlt := hj n (Nat.left_le_pair j (k j))
  rw [dist_zero_right, norm_mul, Complex.norm_natCast, he] at hlt
  have hpos := norm_pos_iff.mpr (hv (Nat.pair j 0))
  have hle : ‖v (Nat.pair j 0)‖⁻¹ ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.right_le_pair j (k j))
  exact (not_lt_of_ge ((inv_le_iff_one_le_mul₀ hpos).mp hle)) (by simpa [mul_comm] using hlt)

/-- Paper: Theorem 10.3.1.1, p. 453. Hardy's theorem supplies infinitely many
ordinates of ordinary Riemann zeta zeros on the critical line. -/
private theorem spectralLineSamples_hardy :
    {t : ℝ | riemannZeta (shift(1 / 2, t)) = 0}.Infinite := by
  sorry

/-- The trivial rational row on the critical line admits a numbering by ℕ. -/
private theorem spectralLineSamples_enumeration :
    Nonempty (ℕ ≃ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2)) := by
  let χ : PontryaginDual C𝔽(ℚ) := 1
  let Z := {z : ℂ | 0 < orderAt(χ, z)}
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  have hfinite : orderAt(χ, (2 : ℂ)) ≠ ⊤ := by
    intro h
    have hp : 0 < orderAt(χ, (2 : ℂ)) := h ▸ WithTop.coe_lt_top (0 : ℤ)
    have := completedHeckeL_continuation_zeros χ _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at this
  have hdisc : Zᶜ ∈ codiscrete ℂ := by
    filter_upwards [hL.meromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
    rcases hz.2 with h | h
    · simp [Z, h]
    · exact (hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
        isPreconnected_univ (mem_univ _) (mem_univ z) hfinite h).elim
  have hZ := (HereditarilyLindelofSpace.isLindelof Z).countable_of_isDiscrete
    (compl_mem_codiscrete_iff.mp hdisc).2
  let U := lineZeros(χ, 1 / 2)
  let : Countable U := (hZ.preimage (f := fun t : ℝ ↦ shift(1 / 2, t))
    (by intro x y h; simpa using congrArg Complex.im h)).to_subtype
  let : Infinite U := (spectralLineSamples_hardy.mono fun t ht ↦
    spectralLineSelection_mem_lineZeros t ht).to_subtype
  exact nonempty_equiv_of_countable

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
Take F = ℚ, the trivial base character and a = 1/2. Modulate a nonzero smooth radial
bump in y = log |g| by exp(icy). Its entire transform has discrete real zeros. Avoid the
countably many frequencies c for which a sample is zero. Place infinitely many samples
vⱼ at increasing nonadjacent indices nⱼ ≥ 1/|vⱼ|, leaving infinitely many ordinates for
the other indices. Then nⱼ|vⱼ| ≥ 1, which violates decay at k = 1. -/
theorem Printed.spectralLineSamples_rapid_for_any_numbering_false :
    ¬ Printed.spectralLineSamples_rapid_for_any_numbering := by
  classical
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let χ' := Function.update χ 1 (1 : PontryaginDual C𝔽(ℚ))
  have htriv : χ' 1 = 1 := Function.update_self ..
  have hχ' : IsSpectralBasepointChoice χ' := by
    intro ω
    by_cases h : ω = 1
    · subst ω
      rw [htriv]
      rfl
    · simpa [χ', Function.update_of_ne h] using hχ ω
  obtain ⟨e⟩ := spectralLineSamples_enumeration
  obtain ⟨φ, hφ⟩ := spectralLineSamples_nonvanishing (fun n ↦ (e n).val)
  let v (n : ℕ) := ∫ g, φ.val g * ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
    (shift(0, (e n).val)) g ∂ideleClassTamagawaMeasure ℚ
  obtain ⟨σ, hσ⟩ := spectralLineSamples_bad_numbering v hφ
  apply hσ
  have h := hall ℚ χ' hχ' (1 / 2) φ 1
  rw [htriv] at h
  simpa only [pow_one, Equiv.trans_apply, v] using h (σ.trans e) 1

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
As printed: for each integration-by-parts order N > 1, one constant bounds all admitted
Mellin derivatives at nonreal strip zeros by the displayed falling factorial over |z|^N.
The order range on p. 455 includes the low orders in (10.3.2.7). The radial Mellin transform
uses the compact character coefficient for the selected component, as on p. 450 after
(10.3.1.17). See `spectralStripConvolution_traceCauchy` and ERRATA F185. -/
def Printed.spectralStripMellinJet_norm_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (a α s : ℝ), 0 ≤ α → 1 < s → ∀ (φ : BruhatCompactSupport C𝔽(F)) (N : ℕ), 1 < N →
      let M (ω : PontryaginDual C₁(F)) (z : ℂ) :=
        ∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ z *
          (∫ k : C₁(F), (ω k : ℂ) * φ.val (τ r * k.val) ∂normOneIdeleClassTamagawaMeasure F)
          ∂positiveRealHaar
      ∃ C : ℝ, 0 < C ∧ ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ),
        b ∈ Icc (-α) α → t ≠ 0 → 0 < orderAt(χ ω, shift(a + b, t)) →
        let mult := (orderAt(χ ω, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min mult floorCut(s) else mult
        ∀ i : ℕ, i < count →
          ‖iteratedDeriv i (M ω) (shift(b, t))‖ ≤
            C * (∏ n ∈ Finset.range N, ((i : ℝ) - (n : ℝ))) / ‖shift(b, t)‖ ^ N

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
Take F = ℚ, the trivial base character, a = 1/2, α = 1, s = 2 and N = 2. Let z = iγ
for the first positive critical-line zeta ordinate γ. The interior multiplicity admits
i = 0. For φ(g) = h(log |g|) exp(−iγ log |g|), with h a nonnegative smooth bump of
positive integral, M(φ)(iγ) has positive norm. The n = 0 factor forces the right-hand
side to vanish for every constant C. -/
theorem Printed.spectralStripMellinJet_norm_le_false :
    ¬ Printed.spectralStripMellinJet_norm_le := by sorry

end RiemannMasullo
