/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import SharpWasserstein.Sharp.Source.Internal
public import SharpWasserstein.Sharp.Source.External
public import SharpWasserstein.Sharp.Source.ReferenceBound
public import SharpWasserstein.RegularizedBrownianSourceData

/-!
# The source estimate (Proposition 3.6)

Proposition 3.6 (`prop:source`) of the paper: for `0 < s ≤ T` and `1 ≤ m ≤ N`, the marginal
sources `ζ^{(m)}_s` of the source `ζ^N_s = -div(R^N_s U_s)` (Section 3.3) satisfy
`E_{R^{(m)}_s}(ζ^{(m)}_s) ≤ (A₀ + A₁/√s)² m²/N²`, where
`A₀ = 2M + L_c e^{LT} √C₀` and `A₁ = √8 M √(C₀ D_T)` (`eq:const3`).

The proof follows Section 4.2 of the paper.
* The source is the flux functional of the reference-minus-particle current
  `U_s = initialCurrent (kernelOf a K) μ_s` (Lemma 4.4, `lem:source-rep`), and every marginal
  source is represented by the conditional current `g^{(m)}_s`. In the development the marginal
  source is the image of the full source under the projection to the first `m` particles, and
  `InitialSourceMarginal.configurationMarginalSource_eq` identifies it with the flux functional
  of `g^{(m)}_s`, so its energy is at most `‖g^{(m)}_s‖²_{L²(R^{(m)}_s)}` (Lemma 3.2).
* `toLp g^{(m)}_s(x)ᵢ = -(N⁻¹ Ξ_s(x)ᵢ + α_m E[c_s(xᵢ, X_{m+1}) | X_{1:m} = x])` (`eq:g`;
  `toLp_marginalCurrent`, `toLp_initialCurrent`).
* Minkowski's inequality in `L²(R^{(m)}_s)` combines the internal part (Lemma 4.5,
  `sqrt_internal_le`) and the external part (Lemma 4.6, `external_le_horizon`):
  `√E ≤ √I_m(s) + √X_m(s) ≤ A₀ m/N + (A₁/√s) m/N`.

## Main statements

* `exists_initial_profile_sharp`: **Proposition 3.6**, in the form of the older
  `RegularizedBrownianSource.exists_initial_profile`, with the constants of the paper.
* `prefixEnergy_le_comparison`: Proposition 3.6 propagated by the existing (non-sharp) hierarchy
  estimate `BrownianEnergyPeriodization.prefixEnergy_quadratic_bound`; the template of the
  endpoint glue producing `SharpWasserstein.Sharp.Endpoint.SharpSourceEnergyBound`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace SharpWasserstein.Sharp.Source

open WeightedTangent InitialSourceMarginal InitialSourcePermutation BrownianPeriodicHierarchy
  RegularizedBrownianSource

variable {d m N : ℕ} {a : Position d → Position d} {K : Position d → Position d → Position d}
  {La L₁ L₂ M : ℝ}

/-! ### The representing field of the marginal sources (Lemma 4.4) -/

/-- The internal interaction sum as the Euclidean vector of a coordinate sum. -/
theorem internalField_eq (q : Measure (Position d)) (x : Configuration d m) (i : Fin m) :
    internalField q K x i = WithLp.toLp 2 (∑ j, (K (x i) (x j) - ∫ y, K (x i) y ∂q)) := by
  simp only [internalField, centred, centredKernel, IsSmoothCoefficients.integral_toLp_K,
    ← WithLp.toLp_sub, ← WithLp.toLp_sum]

/-- The external discrepancy as the Euclidean vector of a coordinate difference. -/
theorem externalField_eq (hm : m < N) (R : Measure (Configuration d N)) [IsProbabilityMeasure R]
    (q : Measure (Position d)) (x : Configuration d m) (i : Fin m) :
    externalField hm R q K x i =
      WithLp.toLp 2 (∫ y, K (x i) y ∂(nextParticleJoint hm R).condKernel x -
        ∫ y, K (x i) y ∂q) := by
  simp only [externalField, IsSmoothCoefficients.integral_toLp_K, ← WithLp.toLp_sub]

/-- The coordinates of the integral of the interaction are the integrals of its coordinates. -/
theorem integral_K_apply (hS : IsSmoothCoefficients a K La L₁ L₂ M) (κ : Measure (Position d))
    [IsFiniteMeasure κ] (u : Position d) (c : Fin d) :
    (∫ y, K u y ∂κ) c = ∫ y, K u y c ∂κ :=
  eval_integral (fun c' =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) c').integrable_comp
      (IsSmoothCoefficients.integrable_K hS κ u)) c

/-- **Lemma 4.4 (`eq:g`), `m < N`.** The conditional current of the first `m` particles (reference
drift minus conditional particle drift) is
`-(N⁻¹ Ξ(x)ᵢ + α_m ∫ K(xᵢ, y) (γ_x - q)(dy))`, `α_m = (N - m)/N`. -/
theorem toLp_marginalCurrent (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hm : m < N)
    (R : Measure (Configuration d N)) [IsProbabilityMeasure R] (q : Measure (Position d))
    [IsProbabilityMeasure q] (x : Configuration d m) (i : Fin m) :
    WithLp.toLp 2 (fun c => nonlinearDrift (kernelOf a K) q (x i) c -
        marginalScalarDrift hm R (kernelOf a K) i c x) =
      -((N : ℝ)⁻¹ • internalField q K x i + (((N : ℝ) - m) / N) • externalField hm R q K x i) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set κ := (nextParticleJoint hm R).condKernel x
  rw [internalField_eq, externalField_eq, ← WithLp.toLp_smul, ← WithLp.toLp_smul,
    ← WithLp.toLp_add, ← WithLp.toLp_neg]
  congr 1
  funext c
  have hint : Integrable (fun y => K (x i) y c) κ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) c).integrable_comp
      (IsSmoothCoefficients.integrable_K hS κ (x i))
  have hκ : ∫ y, kernelOf a K (x i) y c ∂κ = a (x i) c + ∫ y, K (x i) y c ∂κ := by
    simp only [kernelOf, Pi.add_apply]
    rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul]
  simp only [marginalScalarDrift, IsSmoothCoefficients.nonlinearDrift_kernelOf hS q,
    Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.sum_apply]
  rw [hκ, integral_K_apply hS κ]
  simp only [kernelOf, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **Lemma 4.4 (`eq:g`), `m = N`.** The reference-minus-particle current is `-N⁻¹ Ξ(x)ᵢ`. -/
theorem toLp_initialCurrent (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hN : 0 < N)
    (q : Measure (Position d)) [IsProbabilityMeasure q] (x : Configuration d N) (i : Fin N) :
    WithLp.toLp 2 (initialCurrent (kernelOf a K) q x i) = -((N : ℝ)⁻¹ • internalField q K x i) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [internalField_eq, ← WithLp.toLp_smul, ← WithLp.toLp_neg]
  congr 1
  funext c
  simp only [initialCurrent, particleDrift, IsSmoothCoefficients.nonlinearDrift_kernelOf hS q,
    kernelOf, Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-! ### The level energies -/

section Reference

variable {Mb Lb₁ Lb₂ : ℝ}
  (hb : BoundedSmoothKernel (kernelOf a K)) (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂)
  (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution (kernelOf a K) μ)
  (P : Measure (Configuration d N)) [IsProbabilityMeasure P]

/-- `A₀ m/N + (A₁/√s) m/N = (A₀ + A₁/√s) m/N`, and its square. -/
theorem sq_source_bound (A₀ A₁ s : ℝ) (m N : ℕ) :
    (A₀ * m / N + A₁ / √s * (m / N)) ^ 2 = (A₀ + A₁ / √s) ^ 2 * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  ring

/-- **Minkowski's inequality for the marginal current** (proof of Proposition 3.6, `m < N`).
For an arbitrary law `R`, if the internal part satisfies `√I ≤ A₀ m/N` and the external part
satisfies `X ≤ (A₁²/s) m²/N²`, then the squared `L²(R^{(m)})` norm of the conditional current of
the first `m` particles is at most `(A₀ + A₁/√s)² m²/N²`. -/
theorem integral_marginalCurrent_le_of (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hm0 : 0 < m)
    (hm : m < N) (R : Measure (Configuration d N)) [IsProbabilityMeasure R]
    (q : Measure (Position d)) [IsProbabilityMeasure q] {A₀ A₁ s : ℝ} (hA₀ : 0 ≤ A₀)
    (hA₁ : 0 ≤ A₁) (hs : 0 < s)
    (hI : √(((N : ℝ) ^ 2)⁻¹ * ∫ x, ∑ i, ‖internalField q K x i‖ ^ 2 ∂marginal hm.le R) ≤
      A₀ * m / N)
    (hX : (((N : ℝ) - m) / N) ^ 2 * ∫ x, ∑ i, ‖externalField hm R q K x i‖ ^ 2
      ∂marginal hm.le R ≤ A₁ ^ 2 / s * (m : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    ∫ x, ∑ i, ∑ c, (nonlinearDrift (kernelOf a K) q (x i) c -
        marginalScalarDrift hm R (kernelOf a K) i c x) ^ 2 ∂marginal hm.le R ≤
      (A₀ + A₁ / √s) ^ 2 * (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have : IsProbabilityMeasure (marginal hm.le R) :=
    Measure.isProbabilityMeasure_map (measurable_restrictCoordinates hm.le).aemeasurable
  set α : ℝ := ((N : ℝ) - m) / N
  have hN : (0 : ℝ) < N := by exact_mod_cast hm0.trans hm
  have hpt : ∀ x : Configuration d m, ∑ i, ∑ c, (nonlinearDrift (kernelOf a K) q (x i) c -
      marginalScalarDrift hm R (kernelOf a K) i c x) ^ 2 =
      ∑ i, ‖(N : ℝ)⁻¹ • internalField q K x i + α • externalField hm R q K x i‖ ^ 2 := by
    intro x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← norm_neg, ← toLp_marginalCurrent hS hm R q x i, norm_toLp_sq]
  simp_rw [hpt]
  have hmin := sqrt_integral_sum_norm_sq_add_le (μ := marginal hm.le R)
    (f := fun x i => (N : ℝ)⁻¹ • internalField q K x i)
    (g := fun x i => α • externalField hm R q K x i)
    (fun i => by exact (measurable_internalField hS q i).const_smul ((N : ℝ)⁻¹))
    (fun i => by exact (measurable_externalField hS hm R q i).const_smul α)
    (fun x i => (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_internalField_le hS q x i) (norm_nonneg _)))
    (fun x i => (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_externalField_le hS hm R q x i) (norm_nonneg _)))
  rw [integral_sum_norm_smul_sq, integral_sum_norm_smul_sq, inv_pow] at hmin
  have hX' : √(α ^ 2 * ∫ x, ∑ i, ‖externalField hm R q K x i‖ ^ 2 ∂marginal hm.le R) ≤
      A₁ / √s * (m / N) := by
    rw [Real.sqrt_le_left (by positivity)]
    refine hX.trans (le_of_eq ?_)
    rw [mul_pow, div_pow, div_pow, Real.sq_sqrt hs.le]
    ring
  have hsum := hmin.trans (add_le_add hI hX')
  rw [Real.sqrt_le_left (by positivity), sq_source_bound] at hsum
  exact hsum

/-- **The level energy bound for `m < N`** (proof of Proposition 3.6). The squared `L²` norm of
the conditional current of the first `m` particles under `R^{(m)}_s` is at most
`(A₀ + A₁/√s)² m²/N²`: Minkowski's inequality combines Lemmas 4.5 and 4.6. -/
theorem integral_marginalCurrent_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (hP : HasSecondMoment P) (hex : Exchangeable P) {C₀ s U : ℝ} (hC₀ : 0 ≤ C₀) (hs : 0 < s)
    (hsU : s ≤ U)
    (hinit : ∀ j, ∀ hj : j ≤ N, wassersteinSq (marginal hj P) (tensorLaw (μ 0) j) ≤
      ENNReal.ofReal (C₀ * (j : ℝ) ^ 2 / (N : ℝ) ^ 2)) (hm0 : 0 < m) (hm : m < N) :
    haveI := law_isProbabilityMeasure_of_pos hb hbound hMb hLb₁ hμ P hs
    ∫ x, ∑ i, ∑ c, (nonlinearDrift (kernelOf a K) (μ s) (x i) c -
        marginalScalarDrift hm (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s)
          (kernelOf a K) i c x) ^ 2
        ∂marginal hm.le (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) ≤
      (sourceA₀ C₀ U La L₁ L₂ M + sourceA₁ C₀ U La L₁ M / √s) ^ 2 * (m : ℝ) ^ 2 /
        (N : ℝ) ^ 2 := by
  have hA := hS.assumptionA
  have := law_isProbabilityMeasure_of_pos hb hbound hMb hLb₁ hμ P hs
  have := hμ.1 s hs.le
  exact integral_marginalCurrent_le_of hS hm0 hm _ (μ s)
    (sourceA₀_nonneg hA.L₁_nonneg hA.L₂_nonneg hA.M_nonneg) (sourceA₁_nonneg hA.M_nonneg) hs
    (sqrt_internal_le hb hbound hMb hLb₁ hμ P hS hP hs.le hsU hm.le (hinit m hm.le))
    (external_le_horizon hb hbound hMb hLb₁ hμ P hS hP hex hC₀ hs hsU hinit hm0 hm)

/-- **The level energy bound for `m = N`** (proof of Proposition 3.6). The squared `L²` norm of
the reference-minus-particle current under `R^N_s` is at most `(A₀ + A₁/√s)² N²/N²`; at the top
level only the internal part (Lemma 4.5) is present. -/
theorem integral_initialCurrent_le (hS : IsSmoothCoefficients a K La L₁ L₂ M)
    (hP : HasSecondMoment P) (hN : 0 < N) {C₀ s U : ℝ} (hs : 0 < s) (hsU : s ≤ U)
    (hinit : wassersteinSq (marginal le_rfl P) (tensorLaw (μ 0) N) ≤
      ENNReal.ofReal (C₀ * (N : ℝ) ^ 2 / (N : ℝ) ^ 2)) :
    ∫ x, ∑ i, ∑ c, (initialCurrent (kernelOf a K) (μ s) x i c) ^ 2
        ∂PrescribedReference.law hb hbound hMb hLb₁ hμ N P s ≤
      (sourceA₀ C₀ U La L₁ L₂ M + sourceA₁ C₀ U La L₁ M / √s) ^ 2 * (N : ℝ) ^ 2 /
        (N : ℝ) ^ 2 := by
  have hA := hS.assumptionA
  have := hμ.1 s hs.le
  have hpt : ∀ x : Configuration d N, ∑ i, ∑ c, (initialCurrent (kernelOf a K) (μ s) x i c) ^ 2 =
      ∑ i, ‖(N : ℝ)⁻¹ • internalField (μ s) K x i‖ ^ 2 := by
    intro x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← norm_neg, ← toLp_initialCurrent hS hN (μ s) x i, norm_toLp_sq]
  simp_rw [hpt]
  rw [integral_sum_norm_smul_sq, inv_pow]
  have hI := sqrt_internal_le hb hbound hMb hLb₁ hμ P hS hP hs.le hsU le_rfl hinit
  rw [marginal_self] at hI
  have hA₀ := sourceA₀_nonneg (C₀ := C₀) (T := U) (La := La) hA.L₁_nonneg hA.L₂_nonneg
    hA.M_nonneg
  have hA₁ := sourceA₁_nonneg (C₀ := C₀) (T := U) (La := La) (L₁ := L₁) hA.M_nonneg
  rw [Real.sqrt_le_left (by positivity)] at hI
  calc _ ≤ (sourceA₀ C₀ U La L₁ L₂ M * N / N) ^ 2 := hI
    _ = sourceA₀ C₀ U La L₁ L₂ M ^ 2 * (N : ℝ) ^ 2 / (N : ℝ) ^ 2 := by ring
    _ ≤ _ := by
      gcongr
      exact le_add_of_nonneg_right (by positivity)

end Reference

/-! ### Proposition 3.6 -/

/-- The coordinates of the kernel are bounded by its sup-norm bound. -/
theorem abs_kernelOf_le {Mb Lb₁ Lb₂ : ℝ} (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂)
    (u w : Position d) (c : Fin d) : |kernelOf a K u w c| ≤ Mb := by
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (kernelOf a K u w) c).trans (hbound.value u w)

section Proposition

variable {Mb Lb₁ Lb₂ : ℝ}
  (hb : BoundedSmoothKernel (kernelOf a K)) (hbound : KernelBounds (kernelOf a K) Mb Lb₁ Lb₂)
  (hMb : 0 ≤ Mb) (hLb₁ : 0 ≤ Lb₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution (kernelOf a K) μ)
  (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (hP : HasSecondMoment P)

include hP in
/-- **Proposition 3.6 (`prop:source`).** Let `a`, `K` be smooth coefficients with the Euclidean
constants `L_a, L₁, L₂, M` of Assumption A, let `P` be an exchangeable initial law with finite
second moment satisfying the initial hierarchy `W²(P^{(k)}, μ_0^{⊗k}) ≤ C₀ k²/N²` for
`1 ≤ k ≤ N`, and let `0 < s ≤ U`. The source `ζ^N_s = -div(R^N_s U_s)`, carried by the
reference law `R^N_s` and represented by the reference-minus-particle current
`U_s = initialCurrent (kernelOf a K) μ_s`, has finite energy, and all its marginal sources
satisfy `E_{R^{(m)}_s}(ζ^{(m)}_s) ≤ (A₀ + A₁/√s)² m²/N²` for `1 ≤ m ≤ N`, where `A₀`, `A₁` are
the constants of the horizon `U`. The level energies are those of the development
(`levelLaw`, `levelSource`), as in `RegularizedBrownianSource.exists_initial_profile`. -/
theorem exists_initial_profile_sharp (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hN : 0 < N)
    (hex : Exchangeable P) {C₀ s U : ℝ} (hC₀ : 0 ≤ C₀) (hs : 0 < s) (hsU : s ≤ U)
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk P) (tensorLaw (μ 0) k) ≤
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2)) :
    let R := PrescribedReference.law hb hbound hMb hLb₁ hμ N P s
    letI : IsProbabilityMeasure R := law_probability hb hbound hMb hLb₁ hμ P hP hs.le
    ∃ σ₀ : Test (N * d) →ₗ[ℝ] ℝ,
      (∀ φ : Test (N * d), σ₀ φ = ∫ x, ⟪gradient φ.val x,
        euclideanFlux (initialCurrent (kernelOf a K) (μ s)) x⟫_ℝ ∂euclideanLaw R) ∧
      FiniteEnergy (euclideanLaw R) σ₀ ∧
      ∀ m, 1 ≤ m → m ≤ N →
        energy (levelLaw d N (euclideanLaw R) m) (levelSource d N (euclideanLaw R) σ₀ m) ≤
          (sourceA₀ C₀ U La L₁ L₂ M + sourceA₁ C₀ U La L₁ M / Real.sqrt s) ^ 2 *
            (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  intro R
  have := law_probability hb hbound hMb hLb₁ hμ P hP hs.le
  have := hμ.1 s hs.le
  have := hμ.1 0 le_rfl
  have hinit' := initialHierarchy_all hinit
  have hbmeas : Measurable (Function.uncurry (kernelOf a K)) := hb.smooth.continuous.measurable
  have hbnd := abs_kernelOf_le hbound
  have hv := current_memLp hb hbound hMb hLb₁ hμ P hP hN hs.le
  set σ := configurationFluxFunctional R (initialCurrent (kernelOf a K) (μ s)) hv with hσdef
  have hσ : ∀ φ : ConfigurationTest d N, σ φ = ∫ x,
      generator (fun z i => nonlinearDrift (kernelOf a K) (μ s) (z i)) φ.val x -
        generator (particleDrift (kernelOf a K)) φ.val x ∂R := by
    intro φ
    rw [hσdef, configurationFluxFunctional_apply]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [generator_difference, fderiv_eq_sum_coordinateDerivative]
  have hfin := configurationFluxFunctional_finiteEnergy_and_le R _ hv
  refine ⟨euclideanDistribution σ, initialCurrent_distribution_pairing R (μ s) _ σ hσ hv,
    (configurationFiniteEnergy_iff _ _).mp hfin.1, fun m hm1 hmN => ?_⟩
  rw [levelEnergy_eq_configurationMarginal hmN R σ]
  rcases hmN.lt_or_eq with hlt | rfl
  · -- `m < N`: the marginal source is the flux functional of the conditional current.
    have hexR := law_exchangeable hb hbound hMb hLb₁ hμ P hex hs
    let g : Configuration d m → Configuration d m := fun x i c =>
      nonlinearDrift (kernelOf a K) (μ s) (x i) c - marginalScalarDrift hlt R (kernelOf a K) i c x
    have hgm : ∀ i c, Measurable fun x => g x i c := fun i c =>
      (reference_coordinate_measurable (μ s) hbmeas hbnd i c).sub
        (conditional_coordinate_measurable hlt R hbmeas i c)
    have hgb : ∀ i c, ∃ B, ∀ x, |g x i c| ≤ B := fun i c => by
      obtain ⟨C, hC⟩ := conditional_coordinate_bounded hlt R hbmeas hbnd i c
      exact ⟨Mb + C, fun x => (abs_sub _ _).trans
        (add_le_add (reference_coordinate_bound (μ s) hbmeas hbnd _ c) (hC x))⟩
    have hgsq : Integrable (fun x => ∑ i, ∑ c, (g x i c) ^ 2) (marginal hlt.le R) := by
      have : IsProbabilityMeasure (marginal hlt.le R) :=
        Measure.isProbabilityMeasure_map (measurable_restrictCoordinates hlt.le).aemeasurable
      refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun c _ => ?_
      obtain ⟨B, hB⟩ := hgb i c
      refine integrable_bounded_scalar _ ((hgm i c).pow_const 2) (C := B ^ 2) fun x => ?_
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
    have hg : MemLp (euclideanFlux g) 2 (euclideanLaw (marginal hlt.le R)) :=
      memLp_euclideanFlux _ (Measurable.of_eval fun i => Measurable.of_eval fun c => hgm i c) hgsq
    have hζ : ∀ φ : ConfigurationTest d m, configurationFluxFunctional (marginal hlt.le R) g hg φ =
        ∫ x, generator (fun z i => nonlinearDrift (kernelOf a K) (μ s) (z i)) φ.val x -
          generator (fun z i c => marginalScalarDrift hlt R (kernelOf a K) i c z) φ.val x
            ∂marginal hlt.le R := by
      intro φ
      rw [configurationFluxFunctional_apply]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [generator, g, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [configurationMarginalSource_eq hlt R hexR (μ s) hMb hbmeas hbnd σ hσ _ hζ]
    exact ((configurationFluxFunctional_finiteEnergy_and_le _ g hg).2).trans
      (integral_marginalCurrent_le hb hbound hMb hLb₁ hμ P hS hP hex hC₀ hs hsU hinit' hm1 hlt)
  · -- `m = N`: the source itself, whose current is the internal part only.
    rw [configurationMarginalSource_self R (μ s) _ σ hσ hv, marginal_self]
    exact hfin.2.trans (integral_initialCurrent_le hb hbound hMb hLb₁ hμ P hS hP hN hs hsU
      (hinit' _ le_rfl))

include hP in
/-- **Proposition 3.6 propagated by the hierarchy estimate of the development.** Combining
`exists_initial_profile_sharp` (with horizon `T`) with
`BrownianEnergyPeriodization.prefixEnergy_quadratic_bound` bounds the tangent energy of
`SharpWasserstein.Sharp.Endpoint.SharpSourceEnergyBound` for `0 < s ≤ t ≤ T` and `1 ≤ k ≤ N` by
`(A₀ + A₁/√s)² e^{4c(t-s)} k²/N²`, where `c = comparisonConstant d Mb Lb₁ Lb₂` is the rate of the
existing (non-sharp) propagation estimate. Replacing that estimate by the sharp form of
Proposition 3.7, with rate `ω`, in this proof gives `SharpSourceEnergyBound`. -/
theorem prefixEnergy_le_comparison (hS : IsSmoothCoefficients a K La L₁ L₂ M) (hN : 0 < N)
    (hLb₂ : 0 ≤ Lb₂) (hex : Exchangeable P) {C₀ T t s : ℝ} (hC₀ : 0 ≤ C₀) (ht : 0 < t)
    (htT : t ≤ T) (hs : 0 < s) (hst : s ≤ t)
    (hinit : ∀ k (hk : k ≤ N), 1 ≤ k →
      wassersteinSq (marginal hk P) (tensorLaw (μ 0) k) ≤
        ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 / (N : ℝ) ^ 2))
    {k : ℕ} (hk : k ≤ N) (hk1 : 1 ≤ k) :
    letI : IsProbabilityMeasure (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s) :=
      law_probability hb hbound hMb hLb₁ hμ P hP hs.le
    BrownianEnergyPeriodization.prefixEnergy hN hb hbound hMb hLb₁ hLb₂ ht.le
        (euclideanLaw (PrescribedReference.law hb hbound hMb hLb₁ hμ N P s)) hk
        (euclideanFlux (initialCurrent (kernelOf a K) (μ s)))
        (current_memLp hb hbound hMb hLb₁ hμ P hP hN hs.le) (t - s) ≤
      (sourceA₀ C₀ T La L₁ L₂ M + sourceA₁ C₀ T La L₁ M / Real.sqrt s) ^ 2 *
        Real.exp (4 * comparisonConstant d Mb Lb₁ Lb₂ * (t - s)) * (k : ℝ) ^ 2 /
          (N : ℝ) ^ 2 := by
  have := law_probability hb hbound hMb hLb₁ hμ P hP hs.le
  obtain ⟨σ₀, hσ₀, -, hprofile⟩ := exists_initial_profile_sharp hb hbound hMb hLb₁ hμ P hP hS
    hN hex hC₀ hs (hst.trans htT) hinit
  exact BrownianEnergyPeriodization.prefixEnergy_quadratic_bound hN hb hbound hMb hLb₁ hLb₂ ht.le
    _ (law_secondMoment hb hbound hMb hLb₁ hμ P hP hs.le) _
    (law_exchangeable hb hbound hMb hLb₁ hμ P hex hs)
    (current_covariant hb hbound hMb hLb₁ hμ P s) (sq_nonneg _) σ₀ hσ₀ hprofile hk1 hk
    ⟨sub_nonneg.mpr hst, sub_le_self _ hs.le⟩

end Proposition

end SharpWasserstein.Sharp.Source
