module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Baire.CompleteMetrizable
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import RiemannMasullo.ForMathlib.Analysis.Fourier.PoissonSummation
import RiemannMasullo.ForMathlib.Analysis.Fourier.UnitCircle

/-!
# Periodization and Schauder bases on the positive real axis

Masullo, §4.2, pp. 161–174. The logarithmic coordinate is (x = log t).
The circle coordinate is (x / log γ) modulo one.
-/

@[expose] public noncomputable section

open Bornology Function MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff Distributions SchwartzMap

namespace RiemannMasullo

local notation "E" => PositiveRealExponentialDecay (Set.univ : Set ℝ)
local notation "S" => ElementarySchwartz 0 1 0 (PUnit : Type)
local notation "G" => ElementaryLieGroup 0 1 0 (PUnit : Type)
local notation "T" => AddCircle (1 : ℝ)
local notation "point" z => ((0, fun _ : Fin 1 ↦ z, 0, PUnit.unit) : G)
local notation "freq" => Equiv.intEquivNat.symm
local notation "phase[" γ ", " m "]" => (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (Real.log γ : ℂ))

section Periodization

variable (γ : ℝ) (hγ : 1 < γ)

/-- Paper: Definition 4.2.1.1, p. 162. Sum the translates of a logarithmic profile
at a representative of the unit-circle coordinate.
Deviation: The same formula is used on ordinary Schwartz profiles, as in Remark 4.2.2.6. -/
def cyclicPeriodizationValue (_hγ : 1 < γ) (f : 𝓢(ℝ, ℂ)) (g : G) : ℂ :=
  ∑' k : ℤ, f (Real.log γ * ((AddCircle.equivIco 1 0 (g.2.1 0)).val + k))

/-- Paper: Definition 4.2.1.1, p. 162. The sum converges and can be computed at
any real lift of the circle coordinate.
Deviation: This also checks the formula on the ordinary Schwartz space. -/
theorem cyclicPeriodizationValue_hasSum (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f (x + (k : ℝ) * Real.log γ))
      (cyclicPeriodizationValue γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by
  let L := Real.log γ
  have hL : L ≠ 0 := (Real.log_pos hγ).ne'
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (f.compSubConstCLM ℂ (-x))
  have hs : Summable (fun k : ℤ ↦ F (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((F.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  let a (k : ℤ) := f (x + (k : ℝ) * L)
  have ha : Summable a := by
    simpa [a, F, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, add_comm] using hs
  let r := ((AddCircle.equivIco (1 : ℝ) 0) ((x / L : ℝ) : T)).val
  change HasSum a (∑' k : ℤ, f (L * (r + k)))
  have hr : r = x / L - ⌊x / L⌋ := by
    dsimp only [r]
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, ← Int.self_sub_floor]
  convert ha.hasSum using 1
  calc
    (∑' k : ℤ, f (L * (r + k))) = ∑' k : ℤ, a ((Equiv.subRight ⌊x / L⌋) k) := by
      apply tsum_congr
      intro k
      simp only [a, Equiv.subRight_apply, Int.cast_sub, hr]
      congr 1
      field_simp
      ring
    _ = ∑' k : ℤ, a k := (Equiv.subRight ⌊x / L⌋).tsum_eq a

/-- A smooth periodic lift gives an elementary Schwartz function on the circle. -/
private theorem mem_elementarySchwartz_circle_of_contDiff {h : T → ℂ}
    (hs : ContDiff ℝ ∞ (fun x : ℝ ↦ h (x : T))) :
    (fun g : G ↦ h (g.2.1 0)) ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  let X := EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1)
  let φ : G → ℂ := fun g ↦ h (g.2.1 0)
  let L : X →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
  have hφ (a : Fin 0 → ℤ) (b : PUnit) :
      ContDiff ℝ ∞ (fun xt ↦ φ (elementaryCover xt a b)) := hs.comp L.contDiff
  refine ⟨hφ, fun i ↦ ?_⟩
  let s (x : ℝ) : X := (0, x • EuclideanSpace.single 0 1)
  have hsc : Continuous s := continuous_const.prodMk (continuous_id.smul continuous_const)
  let D := elementaryPartial φ i.2.1 i.2.2.1
  have hD := elementaryPartial_descends φ i.2.1 i.2.2.1 0 PUnit.unit (hφ 0 PUnit.unit)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hD.1.continuous.comp hsc).continuousOn
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = PUnit.unit := Subsingleton.elim _ _
  subst a b
  let r := (AddCircle.equivIco (1 : ℝ) 0) (xt.2 0 : T)
  have hr : (r : ℝ) ∈ Icc 0 1 := Ico_subset_Icc_self (by simpa using r.property)
  have he : elementaryCover (s r) (0 : Fin 0 → ℤ) PUnit.unit =
      elementaryCover xt 0 PUnit.unit := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ rfl)
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (↑((r.val • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0) : T) = _
    trans (r.val : T)
    · simp [PiLp.smul_apply]
    · exact AddCircle.coe_equivIco
  have hbound : ‖D xt 0 PUnit.unit‖ ≤ C := by
    dsimp only [D]
    rw [← hD.2 (s r) xt he]
    exact hC r hr
  simp only [Fin.prod_univ_zero, one_mul, ENNReal.coe_nnreal_eq, coe_nnNorm]
  exact ENNReal.ofReal_le_ofReal hbound

/-- Paper: Lemma 4.2.1.5(1), p. 165. The orbit sum gives a smooth function
on the circle.
Deviation: Smoothness also holds on the ordinary Schwartz source. -/
theorem cyclicPeriodizationValue_mem (f : 𝓢(ℝ, ℂ)) :
    cyclicPeriodizationValue γ hγ f ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  let h (z : T) := cyclicPeriodizationValue γ hγ f (point z)
  change (fun g : G ↦ h (g.2.1 0)) ∈ _
  apply mem_elementarySchwartz_circle_of_contDiff
  let L := Real.log γ
  have hL : L ≠ 0 := (Real.log_pos hγ).ne'
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have he : (fun x : ℝ ↦ h (x : T)) = fun x : ℝ ↦ ∑' n : ℤ, F (x + n) := by
    funext x
    simpa [h, F, e, L, hL, (Real.log_pos hγ).ne', add_mul] using
      (cyclicPeriodizationValue_hasSum γ hγ f (x * L)).tsum_eq.symm
  rw [he]
  exact schwartz_contDiff_periodization F

/-- Paper: Lemma 4.2.1.5(2), p. 165. The orbit sum is linear and continuous
in the Schwartz profile.
Deviation: The bundled properties also hold on the ordinary Schwartz source. -/
theorem cyclicPeriodizationValue_spec :
    (∀ f g, cyclicPeriodizationValue γ hγ (f + g) =
      cyclicPeriodizationValue γ hγ f + cyclicPeriodizationValue γ hγ g) ∧
    (∀ (c : ℂ) f, cyclicPeriodizationValue γ hγ (c • f) = c • cyclicPeriodizationValue γ hγ f) ∧
    Continuous (Y := S) (fun f ↦ (⟨cyclicPeriodizationValue γ hγ f,
      cyclicPeriodizationValue_mem γ hγ f⟩ : S)) := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have : (uniformity 𝓢(ℝ, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero 𝓢(ℝ, ℂ)]
    infer_instance
  have he (g : G) : ∃ L : 𝓢(ℝ, ℂ) →L[ℂ] ℂ, ∀ f, L f = cyclicPeriodizationValue γ hγ f g := by
    let r := ((AddCircle.equivIco (1 : ℝ) 0) (g.2.1 0)).val
    let t (k : ℤ) := Real.log γ * (r + k)
    have ht (k : ℤ) : t k = Real.log γ * r + (k : ℝ) * Real.log γ := by dsimp [t]; ring
    let ev (k : ℤ) := (BoundedContinuousFunction.evalCLM ℂ (t k)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
    let P (s : Finset ℤ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := ∑ k ∈ s, ev k
    have hlim : Filter.Tendsto (fun s f ↦ P s f) Filter.atTop
        (𝓝 (fun f ↦ cyclicPeriodizationValue γ hγ f g)) := by
      rw [tendsto_pi_nhds]
      intro f
      have hs : Summable fun k : ℤ ↦ f (t k) := by
        simpa only [ht] using (cyclicPeriodizationValue_hasSum γ hγ f (Real.log γ * r)).summable
      have hP (s : Finset ℤ) : P s f = ∑ k ∈ s, f (t k) := by
        simp only [P, sum_apply]
        rfl
      simp_rw [hP]
      exact hs.hasSum
    exact ⟨continuousLinearMapOfTendsto P hlim, fun _ ↦ rfl⟩
  choose L hL using he
  have hadd (f g : 𝓢(ℝ, ℂ)) : cyclicPeriodizationValue γ hγ (f + g) =
      cyclicPeriodizationValue γ hγ f + cyclicPeriodizationValue γ hγ g := by
    funext x
    simpa only [Pi.add_apply, ← hL] using (L x).map_add f g
  have hsmul (c : ℂ) (f : 𝓢(ℝ, ℂ)) : cyclicPeriodizationValue γ hγ (c • f) =
      c • cyclicPeriodizationValue γ hγ f := by
    funext x
    simpa only [Pi.smul_apply, ← hL] using (L x).map_smul c f
  let A : 𝓢(ℝ, ℂ) →ₗ[ℂ] S :=
    { toFun f := ⟨_, cyclicPeriodizationValue_mem γ hγ f⟩
      map_add' f g := Subtype.ext (hadd f g)
      map_smul' c f := Subtype.ext (hsmul c f) }
  exact ⟨hadd, hsmul, continuous_toElementarySchwartz_of_eval A (fun g ↦ ⟨L g, hL g⟩)⟩

/-- Paper: Remark 4.2.2.6, p. 173. The cyclic orbit sum is a continuous linear
map from ordinary Schwartz profiles to smooth functions on the circle. -/
def cyclicSchwartzPeriodization : 𝓢(ℝ, ℂ) →L[ℂ] S where
  toFun f := ⟨cyclicPeriodizationValue γ hγ f, cyclicPeriodizationValue_mem γ hγ f⟩
  map_add' f g := Subtype.ext ((cyclicPeriodizationValue_spec γ hγ).1 f g)
  map_smul' c f := Subtype.ext ((cyclicPeriodizationValue_spec γ hγ).2.1 c f)
  cont := (cyclicPeriodizationValue_spec γ hγ).2.2

/-- Paper: Remark 4.2.2.6, p. 173. On the ordinary Schwartz space, periodization
has the same absolutely convergent orbit sum on a logarithmic lift. -/
theorem cyclicSchwartzPeriodization_hasSum (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f (x + (k : ℝ) * Real.log γ))
      (cyclicSchwartzPeriodization γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by sorry

/-- Paper: Definition 4.2.1.1, p. 162. Periodization of an exponentially
decaying Schwartz function sums its translates by integer powers of γ.
Deviation: The source is represented by logarithmic profiles and the target
by the elementary Schwartz space on the unit circle. -/
def cyclicPeriodization : E →ₗ[ℂ] S :=
  (cyclicSchwartzPeriodization γ hγ).toLinearMap.comp
    (logExponentialDecayTwist univ ⟨0, mem_univ _⟩)

/-- Paper: (4.2.1.2), p. 162. The periodized value is the sum over the orbit
of any logarithmic lift. The statement records convergence of the series. -/
theorem cyclicPeriodization_hasSum (f : E) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f.val (x + (k : ℝ) * Real.log γ))
      (cyclicPeriodization γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by sorry

end Periodization

section Fourier

/-- Paper: (4.2.1.3), p. 162. The circle Fourier monomial is smooth and
belongs to the elementary Schwartz space. -/
theorem cyclicExponential_mem (m : ℤ) :
    (fun g : G ↦ fourier m (g.2.1 0)) ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  apply mem_elementarySchwartz_circle_of_contDiff
  have hcoe : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  simp only [fourier_coe_apply]
  fun_prop

/-- Paper: (4.2.1.3), p. 162. The exponential system consists of the usual
Fourier monomials in the normalized circle coordinate. -/
def cyclicExponential (m : ℤ) : S :=
  ⟨fun g ↦ fourier m (g.2.1 0), cyclicExponential_mem m⟩

/-- Paper: (4.2.1.3), p. 162. The monomial pulled back to the positive real
axis is the power with exponent (2πim / log γ).
Deviation: The argument x on the cover is the logarithm of the positive variable. -/
theorem cyclicExponential_apply (γ : ℝ) (hγ : 1 < γ) (m : ℤ) (x : ℝ) :
    cyclicExponential m (point ((x / Real.log γ : ℝ) : T)) =
      Complex.exp (phase[γ, m] * (x : ℂ)) := by sorry

/-- Paper: (4.2.1.4), p. 162. The normalized circle Fourier coefficient is
linear and continuous for the smooth topology. -/
theorem cyclicFourierCoeff_spec (m : ℤ) :
    (∀ f g : S, fourierCoeff (fun z : T ↦ (f + g) (point z)) m =
      fourierCoeff (fun z : T ↦ f (point z)) m + fourierCoeff (fun z : T ↦ g (point z)) m) ∧
    (∀ (c : ℂ) (f : S), fourierCoeff (fun z : T ↦ (c • f) (point z)) m =
      c * fourierCoeff (fun z : T ↦ f (point z)) m) ∧
    Continuous (fun f : S ↦ fourierCoeff (fun z : T ↦ f (point z)) m) := by
  let ev (f : S) (z : T) := f (point z)
  have hc (f : S) : Continuous (ev f) := by
    apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
    let s (x : ℝ) := ((0, x • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) :
      EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1))
    have hs : Continuous s := continuous_const.prodMk (continuous_id.smul continuous_const)
    have he (x : ℝ) : elementaryCover (s x) (0 : Fin 0 → ℤ) PUnit.unit = point (x : T) := by
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [elementaryCover, s, PiLp.smul_apply]
    simpa only [Function.comp_def, ev, he] using ((f.property.1 0 PUnit.unit).continuous.comp hs)
  have hInt (f : S) : Integrable (ev f) AddCircle.haarAddCircle :=
    (hc f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hadd (f g : S) : fourierCoeff (ev (f + g)) m = fourierCoeff (ev f) m + fourierCoeff (ev g) m :=
    congrFun (fourierCoeff.add (hInt f) (hInt g)) m
  have hsmul (c : ℂ) (f : S) : fourierCoeff (ev (c • f)) m = c * fourierCoeff (ev f) m :=
    fourierCoeff.const_mul (ev f) c m
  let L : S →ₗ[ℂ] ℂ := { toFun f := fourierCoeff (ev f) m, map_add' := hadd, map_smul' := hsmul }
  let i : ElementarySchwartzIndex 0 1 0 := (0, 0, 0, 0)
  have hp : Continuous (fun f : S ↦ elementarySchwartzSeminorm i f) :=
    (withGeneratingSeminorms_spec _ _).continuous_seminorm i
  refine ⟨hadd, hsmul, (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    Seminorm.continuous_of_le (q := (elementarySchwartzSeminorm i : Seminorm ℂ S)) hp ?_⟩
  intro f
  have hb (z : T) : ‖ev f z‖ ≤ elementarySchwartzSeminorm i f := by
    change (‖ev f z‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
    apply ENNReal.toReal_mono (f.property.2 i).ne
    rw [show i = (0, 0, 0, 0) from rfl, elementarySchwartzBound_zero]
    exact le_iSup (fun g ↦ (‖f g‖₊ : ENNReal)) (point z)
  have h := norm_integral_le_of_norm_le_const (μ := (AddCircle.haarAddCircle : Measure T))
    (f := fun z : T ↦ fourier (-m) z • ev f z)
    (ae_of_all _ fun z ↦ by simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using hb z)
  change ‖fourierCoeff (ev f) m‖ ≤ elementarySchwartzSeminorm i f
  rw [fourierCoeff]
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

/-- Paper: (4.2.1.4), p. 162. The coefficient uses Mathlib's Fourier integral
with probability Haar measure, which absorbs the factor (1 / log γ). -/
def cyclicFourierCoeff (m : ℤ) : StrongDual ℂ S where
  toFun f := fourierCoeff (fun z : T ↦ f (point z)) m
  map_add' := (cyclicFourierCoeff_spec m).1
  map_smul' := (cyclicFourierCoeff_spec m).2.1
  cont := (cyclicFourierCoeff_spec m).2.2

/-- Paper: Lemma 4.2.1.2, p. 162. A monomial has its own coefficient equal to
one and every other coefficient zero. -/
theorem cyclicFourierCoeff_exponential (m n : ℤ) :
    cyclicFourierCoeff m (cyclicExponential n) = if m = n then 1 else 0 := by
  change fourierCoeff (fourier n : C(T, ℂ)) m = _
  rw [fourierCoeff_fourier]
  by_cases h : m = n <;> simp [h]

local notation "CoverSpace" => EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1)
private def circleRestriction (f : S) (z : T) := f (point z)
private def circleCoverLine : ℝ →L[ℝ] CoverSpace :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (0, EuclideanSpace.single 0 1)

private theorem circleCoverLine_proj (xt : CoverSpace) : circleCoverLine (xt.2 0) = xt := by
  refine Prod.ext (Subsingleton.elim _ _) ?_
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp [circleCoverLine, PiLp.smul_apply]

private theorem circleCoverLine_cover (x : ℝ) : elementaryCover (circleCoverLine x) (0 : Fin 0 → ℤ) PUnit.unit =
    point (x : T) := by
  refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ rfl)
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp [elementaryCover, circleCoverLine, PiLp.smul_apply]

private theorem circleRestriction_comp (f : S) :
    (fun x : ℝ ↦ circleRestriction f x) = (fun xt ↦ f (elementaryCover xt 0 PUnit.unit)) ∘ circleCoverLine := by
  funext x
  simp only [comp_apply, circleCoverLine_cover, circleRestriction]

private theorem circleRestriction_smooth (f : S) : ContDiff ℝ ∞ (fun x : ℝ ↦ circleRestriction f x) := by
  rw [circleRestriction_comp]
  exact (f.property.1 0 PUnit.unit).comp circleCoverLine.contDiff

/-- The single torus coordinate identifies the mixed partial on the cover with an ordinary real derivative. -/
private theorem elementaryPartial_circle (f : S) (β : Fin 0 → ℕ) (γ : Fin 1 → ℕ)
    (xt : CoverSpace) (a : Fin 0 → ℤ) (b : PUnit) :
    elementaryPartial f.val β γ xt a b = iteratedDeriv (γ 0) (fun x : ℝ ↦ circleRestriction f x) (xt.2 0) := by
  let v : CoverSpace := (0, EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  let k := γ 0
  let D : List CoverSpace := (List.ofFn (fun i : Fin 0 ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0))).flatten ++
    (List.ofFn (fun i : Fin 1 ↦ List.replicate (γ i) (0, EuclideanSpace.single i 1))).flatten
  have hD : D = List.replicate k v := by
    change [] ++ (List.replicate k v ++ []) = _
    simp
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = PUnit.unit := Subsingleton.elim _ _
  subst a b
  let p (xt : CoverSpace) := f (elementaryCover xt (0 : Fin 0 → ℤ) PUnit.unit)
  have haux (n : ℕ) (hn : n = k) (d : Fin n → CoverSpace) (hd : ∀ j, d j = v) :
      (iteratedFDeriv ℝ n p xt) d = (iteratedFDeriv ℝ k p xt) (fun _ ↦ v) := by
    subst n
    rw [show d = fun _ ↦ v from funext hd]
  change (iteratedFDeriv ℝ D.length p xt) D.get = _
  rw [haux D.length (by simp [hD]) D.get (by intro j; simp [hD, List.get_eq_getElem]),
    circleRestriction_comp, iteratedDeriv_eq_iteratedFDeriv,
    circleCoverLine.iteratedFDeriv_comp_right (f.property.1 0 PUnit.unit) (xt.2 0) (by simp),
    circleCoverLine_proj]
  simp [circleCoverLine, p, v, k]

private def circleJetLM (k : ℕ) : S →ₗ[ℂ] C(T, ℂ) where
  toFun f := unitCircleJet (circleRestriction f) (circleRestriction_smooth f) k
  map_add' f g := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    simp only [unitCircleJet_coe, ContinuousMap.add_apply]
    change iteratedDeriv k ((fun y : ℝ ↦ circleRestriction f y) + (fun y : ℝ ↦ circleRestriction g y)) x = _
    exact iteratedDeriv_add ((circleRestriction_smooth f).of_le (by simp)).contDiffAt
      ((circleRestriction_smooth g).of_le (by simp)).contDiffAt
  map_smul' c f := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    simp only [unitCircleJet_coe, ContinuousMap.smul_apply, RingHom.id_apply]
    change iteratedDeriv k (c • (fun y : ℝ ↦ circleRestriction f y)) x = _
    exact iteratedDeriv_const_smul_field c _

private theorem circleSeminorm_eq_jetNorm (i : ElementarySchwartzIndex 0 1 0) (f : S) :
    elementarySchwartzSeminorm i f = ‖circleJetLM (i.2.2.1 0) f‖ := by
  let k := i.2.2.1 0
  let J := circleJetLM k f
  have he (x : ℝ) : J (x : T) = iteratedDeriv k (fun y : ℝ ↦ circleRestriction f y) x :=
    unitCircleJet_coe (circleRestriction f) (circleRestriction_smooth f) k x
  apply le_antisymm
  · have hb : elementarySchwartzBound f.val i ≤ ENNReal.ofReal ‖J‖ := by
      refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
      simp only [Fin.prod_univ_zero, one_mul, elementaryPartial_circle,
        ENNReal.coe_nnreal_eq, coe_nnNorm]
      apply ENNReal.ofReal_le_ofReal
      simpa only [he] using J.norm_coe_le_norm ((xt.2 0 : ℝ) : T)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal (norm_nonneg J))
  · apply (ContinuousMap.norm_le J (apply_nonneg _ _)).2
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change (‖J (↑x : T)‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
    apply ENNReal.toReal_mono (f.property.2 i).ne
    unfold elementarySchwartzBound
    refine le_iSup_of_le (circleCoverLine x) (le_iSup_of_le (0 : Fin 0 → ℤ) (le_iSup_of_le PUnit.unit ?_))
    simp [elementaryPartial_circle, he, k, circleCoverLine, PiLp.smul_apply]


open scoped NNReal

private theorem circleJetLM_exponential (k : ℕ) (m : ℤ) :
    circleJetLM k (cyclicExponential m) = unitCircleFrequency m ^ k • fourier m := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  exact iteratedDeriv_unitCircle_fourier m k x

private theorem circleJetLM_term (f : S) (k : ℕ) (m : ℤ) :
    circleJetLM k (cyclicFourierCoeff m f • cyclicExponential m) =
      (unitCircleFrequency m ^ k * fourierCoeff (circleRestriction f) m) • fourier m := by
  rw [map_smul, circleJetLM_exponential, smul_smul, mul_comm]
  rfl

private theorem hasSum_circleFourier (f : S) :
    HasSum (fun m : ℤ ↦ cyclicFourierCoeff m f • cyclicExponential m) f := by
  apply ((withGeneratingSeminorms_spec _ _).tendsto_nhds _ f).2
  intro i ε hε
  let k := i.2.2.1 0
  have h := hasSum_unitCircleJet_fourier (circleRestriction f) (circleRestriction_smooth f) k
  filter_upwards [Metric.tendsto_nhds.mp h ε hε] with s hs
  let F : S := ∑ m ∈ s, cyclicFourierCoeff m f • cyclicExponential m
  calc
    _ = ‖circleJetLM k (F - f)‖ := circleSeminorm_eq_jetNorm i (F - f)
    _ < ε := by
      dsimp only [F]
      rw [map_sub, map_sum, show circleJetLM k f = unitCircleJet (circleRestriction f) (circleRestriction_smooth f) k from rfl]
      simpa only [dist_eq_norm, circleJetLM_term] using hs

private def jetIndex (k : ℕ) : ElementarySchwartzIndex 0 1 0 := (0, 0, fun _ ↦ k, 0)

private theorem circleFourier_term_le (i : ElementarySchwartzIndex 0 1 0) (m : ℤ) (f : S) :
    elementarySchwartzSeminorm i (cyclicFourierCoeff m f • cyclicExponential m) ≤
      unitCircleFourierWeight m * ((elementarySchwartzSeminorm i +
        elementarySchwartzSeminorm (jetIndex (i.2.2.1 0 + 2)) : Seminorm ℂ S) f) := by
  let k := i.2.2.1 0
  calc
    _ = ‖circleJetLM k (cyclicFourierCoeff m f • cyclicExponential m)‖ := circleSeminorm_eq_jetNorm i _
    _ = ‖fourierCoeff (unitCircleJet (circleRestriction f) (circleRestriction_smooth f) k) m‖ := by
      rw [circleJetLM_term, norm_smul, fourier_norm, mul_one, unitCircleJet_fourierCoeff]
    _ ≤ unitCircleFourierWeight m * (‖circleJetLM k f‖ + ‖circleJetLM (k+2) f‖) :=
      norm_unitCircleJet_fourierCoeff_le (circleRestriction f) (circleRestriction_smooth f) k m
    _ = _ := congrArg (fun v ↦ unitCircleFourierWeight m * v) (congrArg₂ (· + ·)
      (circleSeminorm_eq_jetNorm i f).symm (circleSeminorm_eq_jetNorm (jetIndex (k+2)) f).symm)


/-- The Fourier term in any continuous seminorm is bounded by one summable weight times
a continuous seminorm of the original function. -/
private theorem exists_circleFourier_term_bound (q : Seminorm ℂ S) (hq : Continuous q) :
    ∃ Q : Seminorm ℂ S, Continuous Q ∧ ∀ (f : S) (m : ℤ),
      q (cyclicFourierCoeff m f • cyclicExponential m) ≤ unitCircleFourierWeight m * Q f := by
  classical
  have hp := withGeneratingSeminorms_spec (elementarySchwartzSubmodule 0 1 0 PUnit.{1}) elementarySchwartzSeminorm
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_sum_of_continuous hp q hq
  let r (i : ElementarySchwartzIndex 0 1 0) : Seminorm ℂ S :=
    elementarySchwartzSeminorm i + elementarySchwartzSeminorm (jetIndex (i.2.2.1 0 + 2))
  let Q : Seminorm ℂ S := C • ∑ i ∈ s, r i
  have hQ : Continuous Q := (Seminorm.continuous_finsetSum (s := s) fun i _ ↦
    (hp.continuous_seminorm i).add (hp.continuous_seminorm (jetIndex (i.2.2.1 0 + 2)))).const_smul C
  refine ⟨Q, hQ, fun f m ↦ ?_⟩
  let t (m : ℤ) := cyclicFourierCoeff m f • cyclicExponential m
  have evalSum (v : Finset (ElementarySchwartzIndex 0 1 0)) (p : ElementarySchwartzIndex 0 1 0 → Seminorm ℂ S)
      (u : S) : (∑ i ∈ v, p i) u = ∑ i ∈ v, p i u := by
    induction v using Finset.induction_on with
    | empty => simp
    | insert i v hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_apply, ih]
  refine (hC (t m)).trans ?_
  change (C : ℝ) * (∑ i ∈ s, (elementarySchwartzSeminorm i : Seminorm ℂ S)) (t m) ≤
    unitCircleFourierWeight m * ((C : ℝ) * (∑ i ∈ s, r i) f)
  rw [evalSum s r f]
  calc
    _ = (C : ℝ) * ∑ i ∈ s, elementarySchwartzSeminorm i (t m) := congrArg ((C : ℝ) * ·)
      (evalSum s (fun i ↦ (elementarySchwartzSeminorm i : Seminorm ℂ S)) (t m))
    _ ≤ (C : ℝ) * ∑ i ∈ s, unitCircleFourierWeight m * r i f := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ circleFourier_term_le i m f) C.coe_nonneg
    _ = _ := by rw [← Finset.mul_sum]; ring

private theorem absolute_circleFourier : SchauderBasis.IsAbsolute
    (cyclicExponential ∘ Equiv.intEquivNat.symm) (cyclicFourierCoeff ∘ Equiv.intEquivNat.symm) := by
  classical
  intro q hq
  obtain ⟨Q, hQ, hbound⟩ := exists_circleFourier_term_bound q hq
  let W : ℝ≥0 := Real.toNNReal (∑' m : ℤ, unitCircleFourierWeight m)
  have hW : (W : ℝ) = ∑' m : ℤ, unitCircleFourierWeight m :=
    Real.coe_toNNReal _ (tsum_nonneg unitCircleFourierWeight_nonneg)
  refine ⟨W • Q, hQ.const_smul W, fun f ↦ ?_⟩
  let t (m : ℤ) := cyclicFourierCoeff m f • cyclicExponential m
  have ht (m : ℤ) : q (t m) ≤ unitCircleFourierWeight m * Q f := hbound f m
  let e := Equiv.intEquivNat.symm
  have hs := summable_unitCircleFourierWeight.mul_right (Q f)
  have htS : Summable fun m : ℤ ↦ q (t m) := .of_nonneg_of_le (fun m ↦ apply_nonneg q (t m)) ht hs
  refine ⟨e.summable_iff.mpr htS, ?_⟩
  change (∑' n : ℕ, q (t (e n))) ≤ (W • Q) f
  rw [e.tsum_eq (fun m ↦ q (t m))]
  refine (htS.tsum_le_tsum ht hs).trans_eq ?_
  rw [tsum_mul_right]
  change _ = (W : ℝ) * Q f
  rw [hW]

/-- Paper: Lemma 4.2.1.2(1), p. 162. The circle exponentials form an absolute
Schauder basis with the Fourier coefficient functionals.
Deviation: The Schauder basis predicates of §4.1 use the natural-number
enumeration of the integer frequencies. -/
theorem cyclicExponential_absoluteBasis :
    IsSchauderBasis (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) ∧
      SchauderBasis.IsAbsolute (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) := by
  refine ⟨⟨?_, ?_⟩, absolute_circleFourier⟩
  · intro m n
    simpa only [comp_apply, ContinuousLinearMap.coe_coe, Equiv.apply_eq_iff_eq]
      using cyclicFourierCoeff_exponential (Equiv.intEquivNat.symm m) (Equiv.intEquivNat.symm n)
  · intro f
    have h := Equiv.intEquivNat.symm.hasSum_iff.mpr (hasSum_circleFourier f)
    exact h.mono_left (SummationFilter.conditional ℕ).le_atTop

/-- A distribution's Fourier series converges uniformly on every bounded set of smooth
functions, by the summable envelope for the primal Fourier terms. -/
private theorem hasSum_circleFourier_dual (l : StrongDual ℂ S) :
    HasSum (fun m : ℤ ↦ l (cyclicExponential m) • cyclicFourierCoeff m) l := by
  let q := (normSeminorm ℂ ℂ).comp l.toLinearMap
  have hq : Continuous q := continuous_norm.comp l.continuous
  obtain ⟨Q, hQ, h⟩ := exists_circleFourier_term_bound q hq
  apply (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (RingHom.id ℂ) ℂ {B : Set S | IsVonNBounded ℂ B}).2
  intro B hB
  obtain ⟨R, _, hR⟩ := (PolynormableSpace.withSeminorms ℂ S).isVonNBounded_iff_seminorm_bounded.mp hB ⟨Q, hQ⟩
  let t (m : ℤ) (f : S) := l (cyclicExponential m) * cyclicFourierCoeff m f
  have hsum (f : S) : HasSum (fun m ↦ t m f) (l f) := by
    refine ((hasSum_circleFourier f).map l l.continuous).congr_fun fun m ↦ ?_
    simp only [t, Function.comp_apply, map_smul, smul_eq_mul, mul_comm]
  have hb (m : ℤ) (f : S) (hf : f ∈ B) : ‖t m f‖ ≤ unitCircleFourierWeight m * R := by
    have ht : q (cyclicFourierCoeff m f • cyclicExponential m) = ‖t m f‖ := by
      change ‖l (cyclicFourierCoeff m f • cyclicExponential m)‖ = _
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [← ht]
    exact (h f m).trans (mul_le_mul_of_nonneg_left (hR f hf).le (unitCircleFourierWeight_nonneg m))
  have hu := tendstoUniformlyOn_tsum (summable_unitCircleFourierWeight.mul_right R) hb
  convert hu using 1
  · funext s f
    change (∑ m ∈ s, (l (cyclicExponential m) • cyclicFourierCoeff m : StrongDual ℂ S)) f = _
    induction s using Finset.induction_on with
    | empty => rfl
    | insert m s hm ih =>
      rw [Finset.sum_insert hm, Finset.sum_insert hm]
      change l (cyclicExponential m) * cyclicFourierCoeff m f + _ = t m f + _
      exact congrArg (t m f + ·) ih
  · exact funext fun f ↦ (hsum f).tsum_eq.symm
  · rfl

/-- Paper: Lemma 4.2.1.2(2), p. 162. Fourier coefficients are an unconditional
Schauder basis of the strong dual, with coordinates given by evaluation on the monomials.
Deviation: Frequencies are enumerated by the natural numbers. -/
theorem cyclicFourierCoeff_unconditionalBasis :
    let ev := fun n : ℕ ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (cyclicExponential (freq n))
    IsSchauderBasis (cyclicFourierCoeff ∘ freq) ev ∧
      SchauderBasis.IsUnconditional (cyclicFourierCoeff ∘ freq) ev := by
  let e := Equiv.intEquivNat.symm
  have hs (l : StrongDual ℂ S) := e.hasSum_iff.mpr (hasSum_circleFourier_dual l)
  refine ⟨⟨?_, fun l ↦ (hs l).mono_left (SummationFilter.conditional ℕ).le_atTop⟩, hs⟩
  intro m n
  change cyclicFourierCoeff (e n) (cyclicExponential (e m)) = _
  rw [cyclicFourierCoeff_exponential]
  simp [eq_comm]

/-- Paper: Lemma 4.2.1.2(3), p. 162. The quotient Fourier coefficient is the
normalized integral of the lift over the multiplicative fundamental interval. -/
theorem cyclicFourierCoeff_interval (γ : ℝ) (hγ : 1 < γ) (f : S) (m : ℤ) :
    cyclicFourierCoeff m f =
      (Real.log γ : ℂ)⁻¹ * ∫ t in (1 : ℝ)..γ,
        f (point ((Real.log t / Real.log γ : ℝ) : T)) *
          Complex.exp (-phase[γ, m] * (Real.log t : ℂ)) / (t : ℂ) := by sorry

-- TODO(paper-gap): The estimate (4.2.1.7) uses m^k for negative frequencies.
-- For f = e₋₁ and k = 1 the printed right-hand side is negative.

end Fourier

section QuotientDual

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [T2Space X] [PolynormableSpace ℂ X]

/-- Paper: Lemma 4.2.1.3, p. 163. Pullback along the quotient embeds the weak dual
and has image the continuous functionals vanishing on the closed subspace. -/
theorem quotientDual_weakEmbedding (M : Submodule ℂ X) (hM : IsClosed (M : Set X)) :
    let pull := fun l : WeakDual ℂ (X ⧸ M) ↦ StrongDual.toWeakDual (l.toStrongDual.comp M.mkQL)
    IsEmbedding pull ∧ range pull = {l | ∀ x ∈ M, l x = 0} := by
  dsimp only
  constructor
  · have he : IsEmbedding (fun l : WeakDual ℂ (X ⧸ M) ↦ (l : (X ⧸ M) → ℂ)) :=
      WeakBilin.isEmbedding (B := topDualPairing ℂ (X ⧸ M)) ContinuousLinearMap.coe_injective
    have hπ := M.mkQ_surjective.isEmbedding_comp (X := ℂ) M.mkQ
    apply Topology.IsEmbedding.of_comp (g := fun l : WeakDual ℂ X ↦ (l : X → ℂ))
      (WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (M.mkQ x))
      WeakDual.coeFn_continuous
    exact hπ.comp he
  · ext l
    constructor
    · rintro ⟨v, rfl⟩ x hx
      change v (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero M).mpr hx, map_zero]
    · intro h
      refine ⟨StrongDual.toWeakDual (M.liftQL l.toStrongDual (fun x hx ↦ h x hx)), ?_⟩
      exact DFunLike.ext _ _ fun _ ↦ rfl

/-- Paper: Lemma 4.2.1.3, p. 163. The image of the quotient adjoint in the
strong dual consists precisely of the functionals vanishing on the subspace. -/
theorem quotientDual_strongRange (M : Submodule ℂ X) (hM : IsClosed (M : Set X)) :
    range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) =
      {l : StrongDual ℂ X | ∀ x ∈ M, l x = 0} := by
  exact (quotientDual_weakEmbedding M hM).2

/-- Paper: Lemma 4.2.1.3(1), p. 163. For a nuclear Fréchet space the quotient
adjoint also embeds the strong dual, with image the same annihilator. -/
theorem quotientDual_strongEmbedding_of_nuclear (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (hN : IsNuclearTVS X) (hF : IsFrechetTVS X) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by sorry

/-- Paper: Lemma 4.2.1.3(2), p. 164. For a Hilbert space the quotient adjoint
embeds the strong dual, with image the annihilator of the closed subspace. -/
theorem quotientDual_strongEmbedding_of_hilbert {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : Submodule ℂ H) (hM : IsClosed (M : Set H)) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  have : CompleteSpace M := hM.completeSpace_coe
  let s : (H ⧸ M) →L[ℂ] H :=
    Mᗮ.subtypeL.comp M.quotientEquivOrthogonal.toLinearIsometry.toContinuousLinearMap
  let r := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ s
  apply Topology.IsEmbedding.of_leftInverse (f := r) _ r.continuous
    (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL).continuous
  intro φ
  ext x
  change φ (M.mkQ ((M.quotientEquivOrthogonal x : Mᗮ) : H)) = φ x
  congr 1
  exact (M.quotientEquivOrthogonal_symm_eq_mk _ (M.quotientEquivOrthogonal x).property).symm.trans
    (M.quotientEquivOrthogonal.symm_apply_apply x)

/-- Paper: Remark 4.2.1.4, p. 164. In a totally reflexive Fréchet space, a
strong embedding of the quotient adjoint implies bounded lifting for the quotient. -/
theorem liftsBoundedSets_of_quotientDual_strongEmbedding (hF : IsFrechetTVS X)
    (hR : ∀ (N : Submodule ℂ X), IsClosed (N : Set X) →
      ∃ e : (X ⧸ N) ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (X ⧸ N)),
        ∀ x l, e x l = l x)
    (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (h : IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL)) :
    LiftsBoundedSets M.mkQL := by sorry

-- TODO(paper-gap): The classification in Remark 4.2.1.4 needs a hypothesis
-- about bounded lifting for all closed-subspace quotients of X.

end QuotientDual

section Kernel

variable (γ : ℝ) (hγ : 1 < γ)

/-- Paper: Lemma 4.2.1.5(2), p. 165. The periodization of exponential profiles
is continuous. Smoothness in part (1) is built into its elementary Schwartz target. -/
theorem cyclicPeriodization_continuous : Continuous (cyclicPeriodization γ hγ) := by sorry

/-- Paper: Lemma 4.2.1.5(2), p. 165. Every smooth quotient function has an
exponentially decaying lift under periodization. -/
theorem cyclicPeriodization_surjective : Surjective (cyclicPeriodization γ hγ) := by sorry

/-- Paper: Lemma 4.2.1.5(2), p. 165. Periodization sends open sets to open sets. -/
theorem cyclicPeriodization_isOpenMap : IsOpenMap (cyclicPeriodization γ hγ) := by sorry

/-- Paper: Lemma 4.2.1.5(2), p. 165. Bundle the periodization and its continuity
as a continuous linear map. -/
def cyclicPeriodizationCLM : E →L[ℂ] S :=
  ⟨cyclicPeriodization γ hγ, cyclicPeriodization_continuous γ hγ⟩

/-- Paper: Lemma 4.2.1.5(2), p. 165. The bundled map gives the periodization
with the same value at every logarithmic lift. -/
theorem cyclicPeriodizationCLM_apply (f : E) (x : ℝ) :
    cyclicPeriodizationCLM γ hγ f (point ((x / Real.log γ : ℝ) : T)) =
      ∑' k : ℤ, f.val (x + (k : ℝ) * Real.log γ) := by sorry

local notation "Φ" => cyclicPeriodizationCLM γ hγ
local notation "Mγ" => LinearMap.ker (ContinuousLinearMap.toLinearMap Φ)
local notation "Q" => E ⧸ Mγ
local notation "desc" => Submodule.liftQL Mγ Φ le_rfl

/-- Paper: Lemma 4.2.1.5(3), p. 165. The kernel is the closed linear span of
the differences between a function and its translate by γ.
Deviation: The difference is expressed in logarithmic coordinates. -/
theorem cyclicPeriodization_ker :
    Mγ = (Submodule.span ℂ {g : E | ∃ f : E,
      ∀ x : ℝ, g.val x = f.val x - f.val (x + Real.log γ)}).topologicalClosure := by sorry

/-- Paper: Lemma 4.2.1.5(3), p. 165. The quotient functional is obtained from
the Fourier coefficient by undoing probability Haar normalization.
Its pullback is the Mellin evaluation at the negative Fourier frequency. -/
def cyclicQuotientMellinCoeff (m : ℤ) : StrongDual ℂ Q :=
  (Real.log γ : ℂ) • (cyclicFourierCoeff m).comp desc

/-- Paper: Lemma 4.2.1.5(3), p. 165. On representatives the quotient functional
is the Mellin integral with exponent −2πim/log γ. -/
theorem cyclicQuotientMellinCoeff_mk (m : ℤ) (f : E) :
    cyclicQuotientMellinCoeff γ hγ m (Submodule.mkQL Mγ f) =
      mellin (fun t ↦ f.val (Real.log t)) (-phase[γ, m]) := by sorry

-- TODO(paper-gap): In the continuity proof, (4.2.1.14) cannot hold for fixed T
-- and arbitrary ε. At t = T γⁿ the term k = -n alone equals T⁻ᴺ.
-- The difference quotient in (4.2.1.17) has the opposite derivative sign.

/-- Paper: Lemma 4.2.1.5(3), p. 165. The Mellin evaluations form an unconditional
Schauder basis on the strong quotient dual. Lemma 4.2.1.3 identifies this dual
with the annihilator with its inherited strong topology. -/
theorem cyclicQuotientMellinCoeff_unconditionalBasis :
    let δ := cyclicQuotientMellinCoeff γ hγ ∘ freq
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ Q),
      IsSchauderBasis δ c ∧ SchauderBasis.IsUnconditional δ c := by sorry

/-- Paper: Remark 4.2.1.6, p. 165. Every bounded subset of a Hausdorff
quotient of the exponential decay space has a bounded lift. -/
theorem positiveRealExponentialDecay_liftsBoundedSets (M : Submodule ℂ E)
    (hM : IsClosed (M : Set E)) : LiftsBoundedSets M.mkQL := by sorry

end Kernel

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient basis of the
strong dual is absolute, with coordinates given by evaluation on the monomials. -/
theorem cyclicFourierCoeff_absolute :
    SchauderBasis.IsAbsolute (cyclicFourierCoeff ∘ freq)
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (cyclicExponential (freq n))) := by sorry

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient functionals
are bounded in the strong dual. -/
theorem cyclicFourierCoeff_bounded :
    IsVonNBounded ℂ (range cyclicFourierCoeff) := by sorry

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient functionals are
equicontinuous as maps on the circle Schwartz space. -/
theorem cyclicFourierCoeff_equicontinuous :
    Equicontinuous (fun m : ℤ ↦ (cyclicFourierCoeff m : S → ℂ)) := by sorry

-- TODO(paper-gap): The proof on p. 169 gives the positive Mellin frequency
-- and drops the Haar normalization factor. Formula (4.2.1.5) fixes both.

/-- Paper: Remark 4.2.1.8, p. 170. Periodization identifies the exponential-decay
quotient with the smooth circle Schwartz space.
Deviation: The source is the quotient by the kernel of the periodization. -/
theorem cyclicPeriodization_quotient_equiv (γ : ℝ) (hγ : 1 < γ) :
    let P := cyclicPeriodizationCLM γ hγ
    ∃ e : (E ⧸ P.ker) ≃L[ℂ] S, ∀ f : E, e (P.ker.mkQL f) = P f := by sorry

/-- Paper: Remark 4.2.1.8, p. 170. The exponential system is regular in
the smooth topology. -/
theorem cyclicExponential_regular :
    SchauderBasis.IsRegular (cyclicExponential ∘ freq) := by sorry

/-- Paper: Remark 4.2.1.8, p. 170. The exponential system is unbounded
in the smooth topology. -/
theorem cyclicExponential_not_bounded :
    ¬ IsVonNBounded ℂ (range cyclicExponential) := by sorry

section CompactSupport

local notation "D[" K "]" => 𝓓_{K}(ℝ, ℂ)
local notation "symmInterval[" a ", " b "]" =>
  Compacts.mk (Icc (Real.log b - Real.log a) (Real.log b + Real.log a)) isCompact_Icc

/-- Paper: §4.2.2, p. 170. A smooth logarithmic profile supported in a fixed
compact set satisfies all exponential Schwartz weights. -/
theorem compactLogProfile_mem (K : Compacts ℝ) (f : D[K]) :
    (f : ℝ → ℂ) ∈ logExponentialDecaySubmodule univ := by
  exact mem_logExponentialDecaySubmodule_of_hasCompactSupport univ f.hasCompactSupport f.contDiff

/-- Paper: §4.2.2, p. 170. Including profiles supported in a fixed compact set
into the exponential decay space is continuous for the uniform derivative topology. -/
theorem compactLogProfile_continuous (K : Compacts ℝ) :
    Continuous (Y := E) (fun f : D[K] ↦ ⟨(f : ℝ → ℂ), compactLogProfile_mem K f⟩) := by sorry

/-- Paper: §4.2.2, p. 170. The inclusion of the fixed-support test space
takes the same function as an exponentially decaying profile.
Deviation: The support set is the logarithmic image of the paper's K. -/
def compactLogProfileInclusion (K : Compacts ℝ) : D[K] →L[ℂ] E where
  toFun f := ⟨(f : ℝ → ℂ), compactLogProfile_mem K f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := compactLogProfile_continuous K

/-- Paper: §4.2.2, p. 170. A decay profile lies in the image of the test
space precisely when its topological support is contained in the designated compact set. -/
theorem compactLogProfileInclusion_range (K : Compacts ℝ) (f : E) :
    f ∈ range (compactLogProfileInclusion K) ↔ tsupport f.val ⊆ (K : Set ℝ) := by sorry

/-- Paper: Theorem 4.2.2.1, p. 170. An entire function is a Fourier integral
of an L² function supported on the indicated interval exactly when it has
the stated exponential type and an L² trace on the real line. -/
theorem paleyWiener_compactInterval (A : ℝ) (hA : 0 < A) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    (∃ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Ioo (-A) A)) ∧
      ∀ z, f z = ∫ x in Ioo (-A) A, F x * Complex.exp (Complex.I * (x : ℂ) * z)) ↔
    ((∃ C : ℝ, 0 < C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      MemLp (fun x : ℝ ↦ f x) 2 volume) := by sorry

-- TODO(paper-gap): The multiplicative restatement following 4.2.2.1
-- uses A directly as an interval endpoint. The endpoint for type A is exp A.

variable (γ : ℝ) (hγ : 1 < γ)

local notation "Φ[" K "]" =>
  ContinuousLinearMap.comp (cyclicPeriodizationCLM γ hγ) (compactLogProfileInclusion K)

-- TODO(paper-gap): Proposition 4.2.2.2(1) asserts surjectivity for all compact K
-- mapping onto the quotient. For K = [1, γ], the class of 1 has only endpoint
-- representatives in K, where every smooth test function supported in K vanishes.

include hγ in
/-- Paper: Proposition 4.2.2.2(1), p. 171. The closed multiplicative interval
of radius a about b covers the quotient when its logarithmic length exceeds log γ.
Deviation: The interval and quotient map are in logarithmic coordinates. -/
theorem cyclicQuotient_surjOn_interval (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    SurjOn (fun x : ℝ ↦ ((x / Real.log γ : ℝ) : T))
      (symmInterval[a, b] : Set ℝ) univ := by sorry

/-- Paper: Proposition 4.2.2.2(1), p. 171. Periodization gives a continuous
linear isomorphism from the fixed-support interval quotient to the smooth circle space.
Deviation: This states the strict-width interval case treated on p. 172. -/
theorem compactIntervalPeriodization_quotient_equiv (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    ∃ e : (D[K] ⧸ P.ker) ≃L[ℂ] S, ∀ f : D[K], e (P.ker.mkQL f) = P f := by sorry

-- TODO(paper-gap): Proposition 4.2.2.2(2) with a = γ, b = 1, and A₀ = γ
-- forces ψ to be supported in {1}. For a nonzero smooth bump u supported
-- in (1, γ), the function x ↦ u(x) - u(γx) is nonzero and in the stated kernel.

include hγ in
/-- Paper: Remark 4.2.2.3, p. 171. A compact set containing a slightly
enlarged translated fundamental interval covers the quotient. -/
theorem cyclicQuotient_surjOn_of_contains (K : Compacts ℝ) (n : ℤ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hK : Icc (n * Real.log γ + Real.log (1 - ε))
      (n * Real.log γ + Real.log (γ + ε)) ⊆ (K : Set ℝ)) :
    SurjOn (fun x : ℝ ↦ ((x / Real.log γ : ℝ) : T)) (K : Set ℝ) univ := by sorry

/-- Paper: Lemma 4.2.2.4, p. 171. The test space with support in a given
compact set is a closed subspace of the exponential decay space. -/
theorem compactLogProfileInclusion_closed (K : Compacts ℝ)
    (hK : (interior (K : Set ℝ)).Nonempty) :
    IsClosed (range (compactLogProfileInclusion K)) := by sorry

/-- Paper: Lemma 4.2.2.4, p. 171. The test space's uniform derivative topology
agrees with the topology inherited from the exponential decay space. -/
theorem compactLogProfileInclusion_isEmbedding (K : Compacts ℝ)
    (hK : (interior (K : Set ℝ)).Nonempty) :
    IsEmbedding (compactLogProfileInclusion K) := by sorry

/-- Paper: Proposition 4.2.2.5(1), p. 173. The Mellin evaluation sequence
is an absolute Schauder basis of the strong quotient dual. This dual is
identified with the annihilator by Lemma 4.2.1.3. -/
theorem cyclicQuotientMellinCoeff_absoluteBasis :
    let δ := cyclicQuotientMellinCoeff γ hγ ∘ freq
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ (cyclicPeriodizationCLM γ hγ).ker)),
      IsSchauderBasis δ c ∧ SchauderBasis.IsAbsolute δ c := by sorry

/-- Paper: Proposition 4.2.2.5(2), p. 173. For an interval wider than a
fundamental interval, all monomials have lifts supported in that same interval,
whose classes are an absolute Schauder basis for the fixed-support quotient. -/
theorem compactIntervalPeriodization_absoluteBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    ∃ u : ℤ → D[K], (∀ m, P (u m) = cyclicExponential m) ∧
      let basis := P.ker.mkQL ∘ u ∘ freq
      let coeff := fun n ↦ (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl)
      IsSchauderBasis basis coeff ∧ SchauderBasis.IsAbsolute basis coeff := by sorry

/-- Paper: Proposition 4.2.2.5(2), p. 173. Descending the restricted Mellin
evaluations gives an absolute Schauder basis of the strong fixed-support quotient dual. -/
theorem compactIntervalPeriodization_dual_absoluteBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    let δ := fun n ↦ (Real.log γ : ℂ) •
      (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl)
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (D[K] ⧸ P.ker)),
      IsSchauderBasis δ c ∧ SchauderBasis.IsAbsolute δ c := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. Periodization on ordinary Schwartz
profiles has a continuous linear right inverse. -/
theorem cyclicSchwartzPeriodization_hasSection :
    ∃ s : S →L[ℂ] 𝓢(ℝ, ℂ), Function.RightInverse s (cyclicSchwartzPeriodization γ hγ) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. Periodization on exponential Schwartz
profiles has a continuous linear right inverse. -/
theorem cyclicPeriodization_hasSection :
    ∃ s : S →L[ℂ] E, Function.RightInverse s (cyclicPeriodizationCLM γ hγ) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. The circle Schwartz space is topologically
and linearly isomorphic to the space of rapidly decreasing integer sequences. -/
theorem cyclicSchwartz_equiv_rapidDecay :
    Nonempty (S ≃L[ℂ] RapidDecaySequence 1) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. The real Schwartz space is topologically
and linearly isomorphic to the space of rapidly decreasing sequences. -/
theorem realSchwartz_equiv_rapidDecay :
    Nonempty (𝓢(ℝ, ℂ) ≃L[ℂ] RapidDecaySequence 1) := by sorry

/-- Paper: Remark 4.2.2.6, p. 174. The kernel of periodization of ordinary
Schwartz functions is topologically and linearly isomorphic to the source. -/
theorem cyclicSchwartzPeriodization_ker_equiv :
    Nonempty ((cyclicSchwartzPeriodization γ hγ).ker ≃L[ℂ] 𝓢(ℝ, ℂ)) := by sorry

/-- Paper: Remark 4.2.2.6, p. 174. The product of two rapid-decay sequence
spaces is topologically and linearly isomorphic to one such space. -/
theorem rapidDecaySequence_prod_equiv :
    Nonempty ((RapidDecaySequence 1 × RapidDecaySequence 1) ≃L[ℂ] RapidDecaySequence 1) := by sorry

end CompactSupport

end RiemannMasullo
