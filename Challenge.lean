/-
Copyright (c) 2026 Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib

/-!
# Challenge: the Gaussian Free Field satisfies the Osterwalder–Schrader axioms

This file states, in Mathlib-only terms, the construction of Euclidean quantum field theory's
simplest interacting-free model: for every spacetime dimension `d ≥ 2` and mass `m > 0`, the
free (massive) **Gaussian Free Field** exists as a probability measure on the tempered
distributions `S'(ℝ^d)` and satisfies all five **Osterwalder–Schrader axioms** — OS0
(analyticity), OS1 (regularity), OS2 (Euclidean invariance), OS3 (reflection positivity), and
OS4 (clustering and ergodicity). By the Osterwalder–Schrader reconstruction theorem, these
axioms are precisely the conditions under which a Euclidean field theory defines a relativistic
quantum field theory satisfying the Wightman axioms.

The measure is pinned down uniquely by the characterization clause of the theorem: its
generating functional is the Gaussian `Z[f] = exp (−½ ⟨f, C f⟩)`, where `C = (−Δ + m²)⁻¹` is
the free covariance, presented here by its proper-time (heat-kernel) integral
`C(x, y) = ∫₀^∞ e^{−t m²} (4πt)^{−d/2} e^{−‖x−y‖²/(4t)} dt` — an elementary closed formula
requiring no operator theory. Without this clause the existence statement would be trivial
(the Dirac measure at `0` satisfies all five axioms); with it, the theorem asserts exactly
that *the free field* satisfies them.

All definitions below are self-contained over Mathlib: the field configuration space and its
cylinder σ-algebra, the generating functionals, the free covariance, time reflection and the
Osterwalder–Schrader star operation, positive-time test functions, time translations, the
mollifier-regularized two-point function, and the five OS axiom predicates. Wherever an
axiom needs a transformed test function — the Euclidean pullback (OS2), the OS star (OS3),
the time translation (OS4 ergodicity), and the mollifier translates of the two-point
function (OS1) and of clustering (OS4) — the transform is *characterised* pointwise rather
than constructed as a Schwartz map, and the `EuclideanPullbackExists`,
`TimeReflectionStarExists`, `TimeTranslationExists`, and `TranslationExists` clauses of the
theorem rule out the vacuous readings. The single `sorry` is the theorem to be proved.

The formulation of the axioms follows Glimm–Jaffe, *Quantum Physics: A Functional Integral
Point of View* (Springer, 1987), ch. 6, stated for probability measures on `S'(ℝ^d)`; OS3 is
the complex star formulation of Osterwalder–Schrader (*Axioms for Euclidean Green's
functions II*, Comm. Math. Phys. 42 (1975) 281–305, axiom E2).
-/

namespace Challenge

open MeasureTheory Complex

noncomputable section

/-! ## Spacetime, test functions, and field configurations -/

/-- Euclidean spacetime of dimension `d`: `ℝ^d` with the Euclidean inner-product structure. -/
abbrev SpaceTime (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Real-valued Schwartz test functions on `ℝ^d`. -/
abbrev TestFunction (d : ℕ) : Type := SchwartzMap (SpaceTime d) ℝ

/-- Complex-valued Schwartz test functions on `ℝ^d`. -/
abbrev TestFunctionℂ (d : ℕ) : Type := SchwartzMap (SpaceTime d) ℂ

/-- Field configurations: tempered distributions `S'(ℝ^d)`, i.e. the continuous dual of
Schwartz space equipped with the weak-* topology. -/
abbrev FieldConfiguration (d : ℕ) := WeakDual ℝ (SchwartzMap (SpaceTime d) ℝ)

/-- The cylinder σ-algebra on the weak dual of a topological vector space: the smallest
σ-algebra making every evaluation map `ω ↦ ω f` Borel-measurable. This is the standard
measurable structure for measures on distribution spaces. -/
instance measurableSpaceWeakDual {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : MeasurableSpace (WeakDual ℝ E) :=
  ⨆ (f : E), (borel ℝ).comap (fun l : WeakDual ℝ E => (l : E →L[ℝ] ℝ) f)

variable {d : ℕ}

/-! ## Pairings and generating functionals -/

/-- The pairing `⟨ω, f⟩` of a tempered distribution with a real test function. -/
def distributionPairing (ω : FieldConfiguration d) (f : TestFunction d) : ℝ := ω f

/-- The generating functional `Z[J] = ∫ e^{i⟨ω, J⟩} dμ(ω)` of a probability measure on field
configurations, evaluated on a real test function `J`. -/
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure (FieldConfiguration d))
    (J : TestFunction d) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure

/-- Postcomposition of a complex test function with an ℝ-linear continuous map `ℂ →L[ℝ] ℝ`
(such as taking real or imaginary parts), yielding a real test function. -/
def schwartz_comp_clm (f : TestFunctionℂ d) (L : ℂ →L[ℝ] ℝ) : TestFunction d :=
  SchwartzMap.mk (fun x => L (f x))
    (ContDiff.comp L.contDiff f.smooth')
    (by
      intro k n
      obtain ⟨C, hC⟩ := f.decay' k n
      use C * ‖L‖
      intro x
      have h_eq : (fun y => L (f y)) = L ∘ f.toFun := rfl
      have h_deriv : iteratedFDeriv ℝ n (L ∘ f.toFun) x =
          L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x) :=
        ContinuousLinearMap.iteratedFDeriv_comp_left L f.smooth'.contDiffAt
          (WithTop.coe_le_coe.mpr le_top)
      rw [h_eq, h_deriv]
      calc ‖x‖ ^ k * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x)‖
          ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f.toFun x‖) := by
            apply mul_le_mul_of_nonneg_left
            exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
            exact pow_nonneg (norm_nonneg _) _
        _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖) := by ring
        _ ≤ ‖L‖ * C := by
            apply mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = C * ‖L‖ := by ring)

/-- Decomposition of a complex test function into its real and imaginary parts, each a real
test function. -/
def complex_testfunction_decompose (f : TestFunctionℂ d) : TestFunction d × TestFunction d :=
  (schwartz_comp_clm f Complex.reCLM, schwartz_comp_clm f Complex.imCLM)

/-- The pairing of a (real) tempered distribution with a complex test function
`f = f_re + i f_im`, defined as `⟨ω, f⟩ = ⟨ω, f_re⟩ + i ⟨ω, f_im⟩`. -/
def distributionPairingℂ_real (ω : FieldConfiguration d) (f : TestFunctionℂ d) : ℂ :=
  let ⟨f_re, f_im⟩ := complex_testfunction_decompose f
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)

/-- The generating functional evaluated on a complex test function:
`Z[J] = ∫ e^{i⟨ω, J⟩} dμ(ω)` with the complexified pairing. -/
def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
    (J : TestFunctionℂ d) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂ_real ω J)) ∂dμ_config.toMeasure

/-! ## The free covariance -/

/-- The heat-kernel radial profile in `d` dimensions:
`H_d(t, r) = (4πt)^{−d/2} · e^{−r²/(4t)}`, the Gauss kernel of `e^{tΔ}` at radius `r`. -/
def heatKernelProfile (d : ℕ) (t r : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t))

/-- The proper-time (Schwinger) representation of the free covariance profile:
`C_S(r) = ∫₀^∞ e^{−t m²} (4πt)^{−d/2} e^{−r²/(4t)} dt`. This is the radial kernel of
`(−Δ + m²)⁻¹` on `ℝ^d`. -/
def properTimeCovariance (d : ℕ) (m r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-t * m ^ 2) * heatKernelProfile d t r

/-- The free covariance kernel `C(x, y)` of the massive free field: the radial proper-time
profile evaluated at `r = ‖x − y‖`. -/
def freeCovariance (d : ℕ) (m : ℝ) (x y : SpaceTime d) : ℝ :=
  properTimeCovariance d m ‖x - y‖

/-- The covariance bilinear form `⟨f, C g⟩ = ∫∫ f(x) C(x, y) g(y) dx dy` on real test
functions. -/
def covarianceForm (d : ℕ) (m : ℝ) (f g : TestFunction d) : ℝ :=
  ∫ x, ∫ y, (f x) * (freeCovariance d m x y) * (g y) ∂volume ∂volume

/-! ## Schwinger functions and the regularized two-point function -/

/-- The `n`-point Schwinger function (correlation function) of a measure on field
configurations: `S_n(f₁, …, fₙ) = ∫ ⟨ω, f₁⟩ ⋯ ⟨ω, fₙ⟩ dμ(ω)`. -/
def SchwingerFunction (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (n : ℕ)
    (f : Fin n → TestFunction d) : ℝ :=
  ∫ ω, (∏ i, distributionPairing ω (f i)) ∂dμ_config.toMeasure

/-- The two-point Schwinger function `S₂(f, g) = ∫ ⟨ω, f⟩ ⟨ω, g⟩ dμ(ω)`, the covariance of
the measure. -/
def SchwingerFunction₂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
    (f g : TestFunction d) : ℝ :=
  SchwingerFunction dμ_config 2 ![f, g]

/-- The L¹-normalized smooth bump function attached to a `ContDiffBump` centered at the
origin, viewed as a Schwartz function (it is smooth with compact support). It integrates
to `1`, so it is a mollifier. -/
def bumpToSchwartz (φ : ContDiffBump (0 : SpaceTime d)) : TestFunction d :=
  (φ.hasCompactSupport_normed (μ := volume)).toSchwartzMap φ.contDiff_normed

/-- The standard mollifier sequence: bumps with outer radius `1/n` (and inner radius
`1/(2n)`), shrinking to the origin as `n → ∞`. -/
def standardBumpSequence (n : ℕ) (hn : n ≠ 0) : ContDiffBump (0 : SpaceTime d) :=
  { rIn := 1 / (2 * n)
    rOut := 1 / n
    rIn_pos := by positivity
    rIn_lt_rOut := by
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have h2n : (0 : ℝ) < 2 * n := by positivity
      have : (2 * (n : ℝ))⁻¹ < (n : ℝ)⁻¹ := inv_strictAnti₀ hn' (by linarith)
      simp only [one_div]
      exact this }

/-! ## Time reflection and the Osterwalder–Schrader star operation -/

/-- Dimensions admitting a time/space split are nonzero, so `(0 : Fin d)` is available. -/
instance instNeZeroOfFactTwoLe [Fact (2 ≤ d)] : NeZero d :=
  ⟨by have h : 2 ≤ d := Fact.out; omega⟩

/-- The time component `x₀` of a spacetime point (the coordinate reflected by `Θ`). -/
abbrev getTimeComponent [Fact (2 ≤ d)] (x : SpaceTime d) : ℝ :=
  x ⟨0, by have h : 2 ≤ d := Fact.out; omega⟩

/-- Time reflection `Θ : (x₀, x̄) ↦ (−x₀, x̄)`: negate the time coordinate, keep the spatial
coordinates. -/
def timeReflection [Fact (2 ≤ d)] (x : SpaceTime d) : SpaceTime d :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))

/-! ## Positive-time test functions -/

/-- A spacetime point has positive time if its time component is positive. -/
def HasPositiveTime [Fact (2 ≤ d)] (x : SpaceTime d) : Prop := getTimeComponent x > 0

/-- The (open) positive-time half-space `{x : x₀ > 0}`. -/
def positiveTimeSet [Fact (2 ≤ d)] : Set (SpaceTime d) := {x | HasPositiveTime x}

/-! ## Time translations -/

/-- Time translation on spacetime points: shift the time coordinate by `s`, keep the spatial
coordinates: `(timeShift s u)₀ = u₀ + s` and `(timeShift s u)ᵢ = uᵢ` for `i ≠ 0`. -/
def timeShift (s : ℝ) (u : SpaceTime d) : SpaceTime d :=
  WithLp.toLp 2 (fun i => if i.val = 0 then u.ofLp i + s else u.ofLp i)

/-! ## The Osterwalder–Schrader axioms -/

/-- **OS0 (Analyticity):** the generating functional is entire in the complex smearing
parameters: for every finite family `J₁, …, Jₙ` of complex test functions, the map
`z ↦ Z[∑ᵢ zᵢ Jᵢ]` is analytic on all of `ℂⁿ`. -/
def OS0_Analyticity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (J : Fin n → TestFunctionℂ d),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      GJGeneratingFunctionalℂ dμ_config (∑ i, z i • J i)) Set.univ

/-- Local integrability of the pointwise two-point function, the additional condition OS1
imposes in the borderline case `p = 2`. The pointwise two-point function `S₂(x)` is the
mollifier limit of smeared covariances `S₂(φₙ(· − x), φₙ)` along the standard bump sequence,
regularized to `0` at the coincident point `x = 0` (where the two-point function of a
quantum field diverges). The translated mollifier `φₙ(· − x)` is characterised pointwise by
the quantified family `smear` rather than constructed as a Schwartz map; the companion
existence clause in the theorem (`TranslationExists`) rules out the vacuous reading. -/
def TwoPointIntegrable (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ smear : ContDiffBump (0 : SpaceTime d) → SpaceTime d → TestFunction d,
    (∀ φ x y, smear φ x y = bumpToSchwartz φ (y - x)) →
    LocallyIntegrable (fun x : SpaceTime d =>
      if x = 0 then 0
      else Filter.limUnder Filter.atTop
        (fun n : ℕ => if hn : n = 0 then 0
          else SchwingerFunction₂ dμ_config (smear (standardBumpSequence n hn) x)
            (bumpToSchwartz (standardBumpSequence n hn)))) volume

/-- **OS1 (Regularity):** the generating functional satisfies an exponential bound
`‖Z[f]‖ ≤ exp (c (‖f‖₁ + ‖f‖ₚᵖ))` for some `1 ≤ p ≤ 2` and `c > 0`; when `p = 2`, the
two-point function is additionally required to be locally integrable. -/
def OS1_Regularity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    (∀ (f : TestFunctionℂ d),
      ‖GJGeneratingFunctionalℂ dμ_config f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖ ^ p ∂volume))) ∧
    (p = 2 → TwoPointIntegrable dμ_config)

/-- **OS2 (Euclidean invariance):** the generating functional is invariant under every
Euclidean motion `x ↦ R x + b` of `ℝ^d`.

The motion acts on test functions by pullback, `(g · f)(x) = f (g⁻¹ x) = f (R⁻¹ (x − b))`.
Rather than *constructing* that pullback as a Schwartz map — which needs the temperate-growth
and antilipschitz apparatus, and is proof development rather than statement — we quantify over
any test function `f'` that agrees with it pointwise. The companion existence clause in the
theorem (`EuclideanPullbackExists`) rules out the reading in which this is vacuous. -/
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (R : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d) (b : SpaceTime d) (f f' : TestFunctionℂ d),
    (∀ x, f' x = f (R.symm (x - b))) →
    GJGeneratingFunctionalℂ dμ_config f = GJGeneratingFunctionalℂ dμ_config f'

/-- Every Euclidean motion really does pull test functions back to test functions, so the
hypothesis of `OS2_EuclideanInvariance` is satisfiable and the axiom has its full force. -/
def EuclideanPullbackExists (d : ℕ) : Prop :=
  ∀ (R : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d) (b : SpaceTime d) (f : TestFunctionℂ d),
    ∃ f' : TestFunctionℂ d, ∀ x, f' x = f (R.symm (x - b))

/-- **OS3 (Reflection positivity):** the generating functional defines a positive
semi-definite Hermitian form on test functions supported at positive time. This is the
complex (star) formulation of Osterwalder–Schrader (1975, axiom E2): for all complex test
functions `f₁, …, fₙ` supported in the positive-time half-space and coefficients
`c₁, …, cₙ ∈ ℂ`, `∑ᵢⱼ c̄ᵢ cⱼ Z[fᵢ − fⱼ*] ≥ 0`, where `(f*)(x) = conj (f (Θ x))` combines
time reflection with complex conjugation.

The support restriction is a plain hypothesis, `tsupport (f i) ⊆ positiveTimeSet`, rather
than a subtype. `f*` is not *constructed* as a Schwartz map — that needs the
isometry-equivalence and temperate-growth apparatus, and is proof development rather than
statement — instead we quantify over any test functions `fstar j` agreeing with
`conj (f j (Θ ·))` pointwise. The companion existence clause in the theorem
(`TimeReflectionStarExists`) rules out the reading in which this is vacuous. -/
def OS3_ReflectionPositivity [Fact (2 ≤ d)]
    (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (f : Fin n → TestFunctionℂ d) (fstar : Fin n → TestFunctionℂ d)
    (c : Fin n → ℂ),
    (∀ i, tsupport (f i) ⊆ positiveTimeSet) →
    (∀ j x, fstar j x = starRingEnd ℂ (f j (timeReflection x))) →
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      GJGeneratingFunctionalℂ dμ_config
        (f i - fstar j)).re

/-- The Osterwalder–Schrader star `(f*)(x) = conj (f (Θ x))` of a test function is again a
test function, so the hypothesis of `OS3_ReflectionPositivity` is satisfiable and the axiom
has its full force. -/
def TimeReflectionStarExists (d : ℕ) [Fact (2 ≤ d)] : Prop :=
  ∀ f : TestFunctionℂ d, ∃ f' : TestFunctionℂ d,
    ∀ x, f' x = starRingEnd ℂ (f (timeReflection x))

/-- **OS4 (Clustering):** correlations of distant regions decay:
`Z[f + T_a g] → Z[f] Z[g]` as the translation `‖a‖ → ∞`, so that widely separated test
functions become statistically independent. The translate `(T_a g)(x) = g(x − a)` is
characterised pointwise by the quantified `g'`; the companion existence clause in the
theorem (`TranslationExists`) rules out the vacuous reading. -/
def OS4_Clustering (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (f g : TestFunction d) (ε : ℝ), ε > 0 → ∃ (R : ℝ), R > 0 ∧
    ∀ (a : SpaceTime d) (g' : TestFunction d), ‖a‖ > R →
      (∀ x, g' x = g (x - a)) →
      ‖GJGeneratingFunctional dμ_config (f + g') -
       GJGeneratingFunctional dμ_config f * GJGeneratingFunctional dμ_config g‖ < ε

/-- Translation really does carry test functions to test functions, so the hypotheses of
`OS4_Clustering` and `TwoPointIntegrable` are satisfiable and those statements have their
full force. -/
def TranslationExists (d : ℕ) : Prop :=
  ∀ (g : TestFunction d) (a : SpaceTime d), ∃ g' : TestFunction d, ∀ x, g' x = g (x - a)

/-- **OS4 (Ergodicity):** for observables `A(ω) = ∑ⱼ zⱼ e^{⟨ω, fⱼ⟩}`, the time average
`(1/T) ∫₀ᵀ A(T_s ω) ds` converges to the expectation `𝔼_μ[A]` in `L²(μ)` as `T → ∞`.

The translated distribution is `⟨T_s ω, g⟩ = ⟨ω, g ∘ timeShift (−s)⟩`. Rather than
*constructing* `g ∘ timeShift (−s)` as a Schwartz map, we quantify over any family
`translate` agreeing with it pointwise, and write the translated observable through the
real/imaginary decomposition of the pairing. The companion existence clause in the theorem
(`TimeTranslationExists`) rules out the reading in which this is vacuous. -/
def OS4_Ergodicity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (translate : ℝ → TestFunction d → TestFunction d),
    (∀ (s : ℝ) (g : TestFunction d) (x : SpaceTime d), translate s g x = g (timeShift s x)) →
    ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → TestFunctionℂ d),
    let μ := dμ_config.toMeasure
    let A : FieldConfiguration d → ℂ := fun ω =>
      ∑ j, z j * Complex.exp (distributionPairingℂ_real ω (f j))
    let Ashift : ℝ → FieldConfiguration d → ℂ := fun s ω =>
      ∑ j, z j * Complex.exp
        ((ω (translate (-s) (complex_testfunction_decompose (f j)).1) : ℂ) +
          Complex.I * (ω (translate (-s) (complex_testfunction_decompose (f j)).2) : ℂ))
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
          Ashift s ω
          - ∫ ω', A ω' ∂μ‖ ^ 2 ∂μ)
      Filter.atTop
      (nhds 0)

/-- Time translation really does carry test functions to test functions, so the hypothesis
of `OS4_Ergodicity` is satisfiable and the axiom has its full force. -/
def TimeTranslationExists (d : ℕ) : Prop :=
  ∀ (s : ℝ) (g : TestFunction d), ∃ g' : TestFunction d, ∀ x, g' x = g (timeShift s x)

/-! ## The theorem -/

/-- **The Gaussian Free Field satisfies the Osterwalder–Schrader axioms, in every dimension
`d ≥ 2`.** For every mass `m > 0` there is a probability measure `μ` on the tempered
distributions `S'(ℝ^d)` — the free (massive) Gaussian Free Field — such that:

* `μ` is uniquely characterized by its generating functional
  `Z[f] = exp (−½ ⟨f, C f⟩)`, where `C = (−Δ + m²)⁻¹` is the free covariance in its
  proper-time form (this clause pins `μ` down: a Gaussian measure is determined by its
  characteristic functional);
* every Euclidean motion pulls test functions back to test functions
  (`EuclideanPullbackExists`), every test function has an Osterwalder–Schrader star
  (`TimeReflectionStarExists`), and time translation and spacetime translation carry test
  functions to test functions (`TimeTranslationExists`, `TranslationExists`), so the
  characterised OS1 integrability, OS2, OS3, and OS4 below have their full force; and
* `μ` satisfies the five Osterwalder–Schrader axioms: OS0 (analyticity), OS1 (regularity),
  OS2 (Euclidean invariance), OS3 (reflection positivity, complex star formulation), and
  OS4 (both clustering and ergodicity).

The dimension hypothesis `2 ≤ d` enters through the time/space split used by OS3 and is
carried as a `Fact` instance so the positive-time apparatus can consume it. -/
theorem gaussianFreeField_satisfies_OS_axioms (d : ℕ) [Fact (2 ≤ d)] (m : ℝ) (hm : 0 < m) :
    ∃ μ : ProbabilityMeasure (FieldConfiguration d),
      (∀ f : TestFunction d,
        GJGeneratingFunctional μ f =
          Complex.exp (-(1 / 2 : ℂ) * ((covarianceForm d m f f : ℝ) : ℂ))) ∧
      EuclideanPullbackExists d ∧ TimeReflectionStarExists d ∧ TimeTranslationExists d ∧
      TranslationExists d ∧
      OS0_Analyticity μ ∧ OS1_Regularity μ ∧ OS2_EuclideanInvariance μ ∧
      OS3_ReflectionPositivity μ ∧ OS4_Clustering μ ∧ OS4_Ergodicity μ := sorry

end

end Challenge
