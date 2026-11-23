module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import RiemannMasullo.Ch10_TraceSpectral.Sec1

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

/-- Paper: Diagram (10.4.3.2), p. 465. Take `F = ℚ`, the trivial isotype,
`s = 4` and a zeta zero `a + iγ` with `γ > 0`. Let `r = exp(π/γ)` and
`G(x) = exp(−πx²)`. Use the test with real factor
`G − (1+r)G(r ·) + rG(r² ·)` and finite factor the indicator of the
integral finite adeles. Both polar values vanish. The Mellin value of its
untwisted theta at `iγ` is proportional to
`Λ(iγ)(1 − r^(−iγ))(1 − r^(1−iγ))` and is nonzero. The same continuous
Mellin functional annihilates the twisted theta closure because
`Λ(a + iγ) = 0`, where `Λ` denotes completed zeta. -/
theorem Printed.spectralLineCompletion_descends_false :
    ¬ Printed.spectralLineCompletion_descends := by sorry

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
