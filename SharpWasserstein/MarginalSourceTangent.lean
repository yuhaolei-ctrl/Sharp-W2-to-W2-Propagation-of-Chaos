import SharpWasserstein.MarginalParticleCurrent
import SharpWasserstein.ConfigurationFlux

/-! The actual disintegrated particle current produces a genuine negative-Sobolev
source distribution and the sharp quadratic source energy profile. This is a
single-time law identity; no spatial regularity of an elliptic optimizer or
weighted-energy time evolution is presumed here. -/

noncomputable section
namespace SharpWasserstein
open MeasureTheory InformationTheory
open scoped ENNReal BigOperators

/-- The genuine marginal-versus-reference generator discrepancy is the divergence
pairing of the current identified from the full particle law. -/
theorem marginal_generator_difference {d m N : ℕ} (hm : m < N)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d} {M : ℝ}
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ u v a, |b u v a| ≤ M)
    (φ : Configuration d m → ℝ) (x : Configuration d m) :
    generator (fun z i a => marginalScalarDrift hm P b i a z) φ x -
      generator (fun z i => nonlinearDrift b r (z i)) φ x =
      ∑ i : Fin m, ∑ a : Fin d,
        marginalSourceCurrent hm P r b i a x * coordinateDerivative φ i a x := by
  simp only [generator, marginalSourceCurrent]
  simp_rw [nonlinearDrift_coordinate r hb hbound]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- Actual KL and quadratic marginal entropy bounds imply existence of the real
weighted `H⁻¹` generator source, with its claimed Euclidean energy bound. -/
theorem exists_marginalSourceDistribution {d m N : ℕ} {H M : ℝ}
    [MeasurableSpace (WeightedTangent.Point (m * d))]
    [BorelSpace (WeightedTangent.Point (m * d))]
    (hm0 : 0 < m) (hm : m < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d}
    (hex : Exchangeable P) (hfinite : klDiv P (tensorLaw r N) ≠ ∞)
    (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ u v a, |b u v a| ≤ M)
    (hprofile : ∀ j, j ≤ N → marginalEntropy P r j ≤ H * (j : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    ∃ σ : ConfigurationTest d m →ₗ[ℝ] ℝ,
      (∀ φ : ConfigurationTest d m, σ φ =
        ∫ x, ∑ i : Fin m, ∑ a : Fin d,
          marginalSourceCurrent hm P r b i a x * coordinateDerivative φ.val i a x
          ∂marginal hm.le P) ∧
      (∀ φ : ConfigurationTest d m, σ φ =
        ∫ x, generator (fun z i a => marginalScalarDrift hm P b i a z) φ.val x -
          generator (fun z i => nonlinearDrift b r (z i)) φ.val x ∂marginal hm.le P) ∧
      ConfigurationFiniteEnergy (marginal hm.le P) σ ∧
      configurationTangentEnergy (marginal hm.le P) σ ≤
        (2 * (d * internalSourceConstant M) * (1 + H) + 16 * d * M ^ 2 * H) *
          (m : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  let v : Configuration d m → Configuration d m := fun x i a =>
    marginalSourceCurrent hm P r b i a x
  have hvmeas : Measurable v := measurable_pi_lambda _ (fun i =>
    measurable_pi_lambda _ (fun a => measurable_marginalSourceCurrent hm P r hb i a))
  have hsq := marginalSourceSquare_integrable_and_le_profile hm0 hm hex hfinite
    hH hM hb hbound hprofile
  have hv : MemLp (euclideanFlux v) 2 (euclideanLaw (marginal hm.le P)) :=
    memLp_euclideanFlux _ hvmeas hsq.1
  let σ := configurationFluxFunctional (marginal hm.le P) v hv
  have henergy := configurationFluxFunctional_finiteEnergy_and_le (marginal hm.le P) v hv
  refine ⟨σ, ?_, ?_, henergy.1, henergy.2.trans hsq.2⟩
  · exact configurationFluxFunctional_apply (marginal hm.le P) v hv
  · intro φ
    rw [configurationFluxFunctional_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    exact (marginal_generator_difference hm P r hb hbound φ.val x).symm

/-- The full-particle endpoint is realized as the actual generator source as well;
its external conditional term vanishes without ever creating a fictitious particle. -/
theorem exists_fullSourceDistribution {d N : ℕ} {H M : ℝ}
    [MeasurableSpace (WeightedTangent.Point (N * d))]
    [BorelSpace (WeightedTangent.Point (N * d))]
    (hN : 0 < N)
    {P : Measure (Configuration d N)} [IsProbabilityMeasure P]
    {r : Measure (Position d)} [IsProbabilityMeasure r]
    {b : Position d → Position d → Position d}
    (hfinite : klDiv P (tensorLaw r N) ≠ ∞) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ u v a, |b u v a| ≤ M)
    (hprofile : ∀ j, j ≤ N → marginalEntropy P r j ≤ H * (j : ℝ) ^ 2 / (N : ℝ) ^ 2) :
    ∃ σ : ConfigurationTest d N →ₗ[ℝ] ℝ,
      (∀ φ : ConfigurationTest d N, σ φ =
        ∫ x, generator (particleDrift b) φ.val x -
          generator (fun z i => nonlinearDrift b r (z i)) φ.val x ∂P) ∧
      ConfigurationFiniteEnergy P σ ∧
      configurationTangentEnergy P σ ≤ (d * internalSourceConstant M) * (1 + H) := by
  let v : Configuration d N → Configuration d N :=
    fun x i a => particleDrift b x i a - nonlinearDrift b r (x i) a
  have hvcoord (i : Fin N) (a : Fin d) : (fun x => v x i a) =
      fun x => (N : ℝ)⁻¹ * internalScalarCurrent r (fun u w => b u w a) i x :=
    funext (fun x => fullSourceCurrent_eq_internal hN r hb hbound x i a)
  have hvmeas : Measurable v := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro a
    rw [hvcoord i a]
    exact measurable_const.mul (measurable_internalScalarCurrent (r := r)
      (b := fun u w => b u w a) ((measurable_pi_apply a).comp hb) i)
  have hsq : Integrable (fun x => ∑ i, ∑ a, (v x i a) ^ 2) P := by
    simp_rw [show ∀ x i a, v x i a =
      (N : ℝ)⁻¹ * internalScalarCurrent r (fun u w => b u w a) i x from
      fun x i a => fullSourceCurrent_eq_internal hN r hb hbound x i a, mul_pow,
      ← Finset.mul_sum]
    exact (integrable_finsetSum _ (fun i _ =>
      integrable_internalCurrentSquare hb hbound i P)).const_mul _
  have hv := memLp_euclideanFlux P hvmeas hsq
  let σ := configurationFluxFunctional P v hv
  have henergy := configurationFluxFunctional_finiteEnergy_and_le P v hv
  refine ⟨σ, ?_, henergy.1, henergy.2.trans
    (fullSourceSquare_le_profile hN hfinite hH hM hb hbound hprofile)⟩
  intro φ
  rw [configurationFluxFunctional_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [v, generator, sub_mul, Finset.sum_sub_distrib]
  ring

end SharpWasserstein
