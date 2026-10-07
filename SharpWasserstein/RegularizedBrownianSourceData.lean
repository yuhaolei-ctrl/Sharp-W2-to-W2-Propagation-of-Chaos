module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedBrownianSourceCoordinates
public import SharpWasserstein.PrescribedEntropyProfile

@[expose] public section

/-! The supplied nonlinear reference law supplies all initial data for the
sharp Brownian source hierarchy. Entropy regularization, current covariance,
and the one-source marginal energy profile are proved from the original
Wasserstein profile, rather than postulated at the switch time. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal ENNReal
namespace SharpWasserstein.RegularizedBrownianSource
open WeightedTangent InitialSourceMarginal InitialSourcePermutation BrownianPeriodicHierarchy

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)
  (P : Measure (Configuration d N)) [IsProbabilityMeasure P] (hP : HasSecondMoment P)

include hP in
/-- A stable probability witness for the actual prescribed regularized law. -/
theorem law_probability {s : ℝ} (hs : 0 ≤ s) :
    IsProbabilityMeasure (PrescribedReference.law hb hbound hM hL₁ hμ N P s) :=
  (PrescribedReference.law_weakEvolution hb hbound hM hL₁ hμ N P hP).probability s hs

include hP in
/-- The actual law at a nonnegative time has its required second moment. -/
theorem law_secondMoment {s : ℝ} (hs : 0 ≤ s) :
    HasSecondMoment (PrescribedReference.law hb hbound hM hL₁ hμ N P s) :=
  (PrescribedReference.law_weakEvolution hb hbound hM hL₁ hμ N P hP).secondMoment s hs

/-- Independent reference evolution preserves the given initial exchangeability. -/
theorem law_exchangeable (hex : Exchangeable P) {s : ℝ} (hs : 0 < s) :
    Exchangeable (PrescribedReference.law hb hbound hM hL₁ hμ N P s) := by
  rw [PrescribedReference.law_eq_decoupled hb hbound hM hL₁ hμ N P hs]
  exact DecoupledFlow.brownianLaw_exchangeable _ _ _ hs.le P hex

include hP in
/-- The actual reference-minus-particle current is square integrable at the
regularized law; its diagonal interaction is included. -/
theorem current_memLp (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) :
    MemLp (euclideanFlux (initialCurrent b (μ s))) 2
      (euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P s)) := by
  letI := law_probability hb hbound hM hL₁ hμ P hP hs
  letI := hμ.1 s hs
  exact initialCurrent_memLp hN _ _ hb.smooth.continuous.measurable
    (fun x y a => (by simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (b x y) a).trans (hbound.value x y)))

omit [IsProbabilityMeasure P] in
/-- The very same actual current is pointwise covariant, hence covariant
almost everywhere for each initial carrying measure. -/
theorem current_covariant (s : ℝ) (e : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂euclideanLaw (PrescribedReference.law hb hbound hM hL₁ hμ N P s),
      euclideanFlux (initialCurrent b (μ s)) (PropagatedSourcePermutation.euclideanPermutation e x) =
      PropagatedSourcePermutation.euclideanPermutation e (euclideanFlux (initialCurrent b (μ s)) x) :=
  Eventually.of_forall (euclidean_initialCurrent_covariant b (μ s) e)

/-- One actual initial distribution supplies the sharp initial profile at
all levels, and its sign agrees with the switch derivative. -/
theorem exists_initial_profile (hN : 0 < N) (hex : Exchangeable P)
    {C₀ s U : ℝ} (hC₀ : 0 ≤ C₀) (hs : 0 < s) (hsU : s ≤ U)
    (hinit : ∀ j,∀ hj : j ≤ N,wassersteinSq (marginal hj P) (tensorLaw (μ 0) j) ≤
      ENNReal.ofReal (C₀*(j:ℝ)^2/(N:ℝ)^2)) :
    let R := PrescribedReference.law hb hbound hM hL₁ hμ N P s
    letI : IsProbabilityMeasure R := law_probability hb hbound hM hL₁ hμ P hP hs.le
    ∃ σ₀ : Test (N*d) →ₗ[ℝ] ℝ,
      (∀ φ : Test (N*d),σ₀ φ = ∫ x,⟪gradient φ.val x,euclideanFlux (initialCurrent b (μ s)) x⟫_ℝ ∂euclideanLaw R) ∧
      FiniteEnergy (euclideanLaw R) σ₀ ∧
      ∀ m,1 ≤ m → m ≤ N →
        energy (levelLaw d N (euclideanLaw R) m) (levelSource d N (euclideanLaw R) σ₀ m) ≤
          RegularizationRates.sourceHorizonConstant d M C₀ (Real.sqrt (d:ℝ)*L₁) U*
            (1+1/s)*(m:ℝ)^2/(N:ℝ)^2 := by
  letI := hμ.1 0 le_rfl
  letI := law_probability hb hbound hM hL₁ hμ P hP hs.le
  obtain ⟨σ,hσ,hfinite,hprofile⟩ := exists_regularized_consistent_source
    (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ)
    (PrescribedReference.singleDrift_bound hbound hM hμ)
    (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ)
    hN P (μ 0) hP (IsLimitEvolution.initial_integrable_positionSq hμ) hex
    (euclideanDrift_lipschitz_of_sup (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ))
    hs hsU hC₀ hinit hM hb.smooth.continuous.measurable
    (fun x y a => (by simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (b x y) a).trans (hbound.value x y)))
  rw [PrescribedReference.singleBrownianLaw_eq_supplied hb hbound hM hL₁ hμ hs] at hσ
  have hR : DecoupledFlow.brownianLaw
      (PrescribedReference.singleDrift_continuous hb hbound hL₁ hμ)
      (PrescribedReference.singleDrift_bound hbound hM hμ)
      (PrescribedReference.singleDrift_lipschitz hb hbound hL₁ hμ) hs.le P =
      PrescribedReference.law hb hbound hM hL₁ hμ N P s :=
    (PrescribedReference.law_eq_decoupled hb hbound hM hL₁ hμ N P hs).symm
  rw [hR] at hσ hfinite
  refine ⟨euclideanDistribution σ,?_,(configurationFiniteEnergy_iff _ _).mp hfinite,?_⟩
  · exact initialCurrent_distribution_pairing _ _ b σ hσ (current_memLp hb hbound hM hL₁ hμ P hP hN hs.le)
  · intro m hm hmN
    calc
      _ = energy (levelLaw d N (euclideanLaw (DecoupledFlow.brownianLaw _ _ _ hs.le P)) m)
          (levelSource d N (euclideanLaw (DecoupledFlow.brownianLaw _ _ _ hs.le P))
            (euclideanDistribution σ) m) :=
        levelEnergy_measure_congr _ _ (congrArg euclideanLaw hR.symm) _ m
      _ = _ := levelEnergy_eq_configurationMarginal hmN _ σ
      _ ≤ _ := (hprofile m hm hmN).2

end SharpWasserstein.RegularizedBrownianSource
