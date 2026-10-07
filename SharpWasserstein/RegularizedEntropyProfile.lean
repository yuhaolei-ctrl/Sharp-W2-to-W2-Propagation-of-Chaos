module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianDecoupledFlow
public import SharpWasserstein.MarginalMoments

@[expose] public section

/-! # Actual all-level entropy regularization
The initial Wasserstein profile is carried by the constructed decoupled
Brownian flow into the tensor-reference relative-entropy profile used by the
source estimate. Tensorization and marginal commutation are proved identities. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal BigOperators
namespace SharpWasserstein.DecoupledFlow

variable {d : ℕ} {v : ℝ → Position d → Position d} {M K L : ℝ≥0} {T : ℝ}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

/-- The actual independent-Brownian decoupled law at the given horizon. -/
def brownianLaw {N : ℕ} (hT : 0 ≤ T) (P : Measure (Configuration d N)) :
    Measure (Configuration d N) := law hv hb hl hT P (BrownianNoise.positionLaw d T) T

instance brownianLaw_isProbability {N : ℕ} (hT : 0 ≤ T)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (brownianLaw hv hb hl hT P) := law_probability hv hb hl hT P _ ⟨hT, le_rfl⟩

/-- One-particle Brownian transition applied to its initial law. -/
def singleBrownianLaw (hT : 0 ≤ T) (r : Measure (Position d)) : Measure (Position d) :=
  (r.prod (BrownianNoise.positionLaw d T)).map
    (fun p ↦ BoundedFlow.flow hv hb hl hT p.1 p.2 T)

instance singleBrownianLaw_isProbability (hT : 0 ≤ T) (r : Measure (Position d)) [IsProbabilityMeasure r] :
    IsProbabilityMeasure (singleBrownianLaw hv hb hl hT r) :=
  Measure.isProbabilityMeasure_map (BoundedFlow.flow_continuous hv hb hl hT ⟨hT, le_rfl⟩).measurable.aemeasurable

theorem brownianLaw_tensor (hT : 0 ≤ T) (r : Measure (Position d)) [IsProbabilityMeasure r] (N : ℕ) :
    brownianLaw hv hb hl hT (tensorLaw r N) = tensorLaw (singleBrownianLaw hv hb hl hT r) N :=
  law_tensor hv hb hl hT r _ ⟨hT, le_rfl⟩

theorem brownianLaw_marginal {m N : ℕ} (hm : m ≤ N) (hT : 0 ≤ T)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] :
    marginal hm (brownianLaw hv hb hl hT P) = brownianLaw hv hb hl hT (marginal hm P) :=
  law_marginal hv hb hl hm hT P _ ⟨hT, le_rfl⟩

theorem brownianLaw_exchangeable {N : ℕ} (hT : 0 ≤ T)
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (hP : Exchangeable P) :
    Exchangeable (brownianLaw hv hb hl hT P) := law_exchangeable hv hb hl hT P hP _ ⟨hT, le_rfl⟩

/-- Genuine entropy regularization of the constructed decoupled law,
with the same Euclidean Lipschitz constant at every particle level. -/
theorem brownianLaw_entropy_le {N : ℕ} (P Q : Measure (Configuration d N))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : HasSecondMoment P) (hQ : HasSecondMoment Q)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) (hT : 0 < T) :
    klDiv (brownianLaw hv hb hl hT.le P) (brownianLaw hv hb hl hT.le Q) ≤
      ENNReal.ofReal (RegularizationRates.bridgeCost L T) * wassersteinSq P Q := by
  have h := BrownianEntropy.flow_entropy_le_wassersteinSq P Q hP hQ
    (liftDrift_continuous N hv) (liftDrift_bound N hb) (liftDrift_lipschitz N hl)
    (liftDrift_euclidean_lipschitz N he) hT
  rwa [brownian_flowLaw_eq hv hb hl hT P, brownian_flowLaw_eq hv hb hl hT Q] at h

/-- Positive time makes the full tensor-reference entropy finite for every
initial probability law with finite second moment. -/
theorem brownianLaw_entropy_finite {N : ℕ}
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hP : HasSecondMoment P) (hr : Integrable positionSq r)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) (hT : 0 < T) :
    klDiv (brownianLaw hv hb hl hT.le P)
      (tensorLaw (singleBrownianLaw hv hb hl hT.le r) N) < ∞ := by
  rw [← brownianLaw_tensor]
  exact (brownianLaw_entropy_le hv hb hl P (tensorLaw r N) hP
    (hasSecondMoment_tensorLaw r hr N) he hT).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (wassersteinSq_lt_top P (tensorLaw r N) hP (hasSecondMoment_tensorLaw r hr N)))

/-- The finite entropy hierarchy conditions are consequences of the actual
regularized law, including proved monotonicity of its entropy increments. -/
theorem brownianLaw_finiteEntropyConditions {N : ℕ}
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hP : HasSecondMoment P) (hr : Integrable positionSq r) (hex : Exchangeable P)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) (hT : 0 < T) :
    FiniteEntropyConditions
      (marginalEntropy (brownianLaw hv hb hl hT.le P) (singleBrownianLaw hv hb hl hT.le r)) N :=
  exchangeable_finiteEntropyConditions (brownianLaw_exchangeable hv hb hl hT.le P hex)
    (brownianLaw_entropy_finite hv hb hl P r hP hr he hT).ne

/-- All actual marginal entropies acquire the quadratic initial transport
profile after any positive regularization time. -/
theorem regularized_marginal_klDiv_le {N : ℕ}
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hP : HasSecondMoment P) (hr : Integrable positionSq r)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) (hT : 0 < T)
    {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hinit : ∀ m, ∀ hm : m ≤ N, wassersteinSq (marginal hm P) (tensorLaw r m) ≤
      ENNReal.ofReal (C₀ * (m : ℝ)^2 / (N : ℝ)^2)) (m : ℕ) (hm : m ≤ N) :
    klDiv (marginal hm (brownianLaw hv hb hl hT.le P))
      (tensorLaw (singleBrownianLaw hv hb hl hT.le r) m) ≤
      ENNReal.ofReal ((RegularizationRates.bridgeCost L T * C₀) * (m : ℝ)^2 / (N : ℝ)^2) := by
  rw [brownianLaw_marginal, ← brownianLaw_tensor]
  have h := brownianLaw_entropy_le hv hb hl (marginal hm P) (tensorLaw r m)
    (hasSecondMoment_marginal hm hP) (hasSecondMoment_tensorLaw r hr m) he hT
  have hc : 0 ≤ RegularizationRates.bridgeCost L T := by
    unfold RegularizationRates.bridgeCost
    positivity
  calc
    _ ≤ ENNReal.ofReal (RegularizationRates.bridgeCost L T) *
        ENNReal.ofReal (C₀ * (m : ℝ)^2 / (N : ℝ)^2) :=
      h.trans (mul_le_mul_right (hinit m hm) _)
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; ring

/-- The real entropy sequence used by the source modules is the actual
marginal KL sequence, and satisfies the proved all-level profile. -/
theorem regularized_entropy_profile {N : ℕ}
    (P : Measure (Configuration d N)) [IsProbabilityMeasure P]
    (r : Measure (Position d)) [IsProbabilityMeasure r]
    (hP : HasSecondMoment P) (hr : Integrable positionSq r)
    (he : ∀ t, LipschitzWith L (GaussianBridge.euclideanDrift v t)) (hT : 0 < T)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hinit : ∀ m, ∀ hm : m ≤ N, wassersteinSq (marginal hm P) (tensorLaw r m) ≤
      ENNReal.ofReal (C₀ * (m : ℝ)^2 / (N : ℝ)^2)) (m : ℕ) (hm : m ≤ N) :
    marginalEntropy (brownianLaw hv hb hl hT.le P) (singleBrownianLaw hv hb hl hT.le r) m ≤
      (RegularizationRates.bridgeCost L T * C₀) * (m : ℝ)^2 / (N : ℝ)^2 := by
  rw [marginalEntropy_eq hm]
  apply ENNReal.toReal_le_of_le_ofReal
  · unfold RegularizationRates.bridgeCost
    positivity
  · exact regularized_marginal_klDiv_le hv hb hl P r hP hr he hT hC₀ hinit m hm

end SharpWasserstein.DecoupledFlow
