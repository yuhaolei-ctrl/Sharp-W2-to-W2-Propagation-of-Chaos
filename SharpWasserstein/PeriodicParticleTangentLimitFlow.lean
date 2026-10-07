module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowJacobianDriftSmooth
public import SharpWasserstein.PeriodicParticleDerivative
public import SharpWasserstein.ParticleWeakIdentification
public import SharpWasserstein.PropagatedSourceEquationLaw

@[expose] public section

/-! Actual initial-Jacobian convergence for the sine-periodized interacting
particle flows in the unnormalized Euclidean configuration norm. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology ContDiff
namespace SharpWasserstein.PeriodicParticleTangentLimit
open WeightedTangent NoiseAverage FlowInitialDerivative PropagatedSourceEquation

/-- The real interacting drift under the fixed Euclidean coordinate map. -/
def drift {d N : ℕ} (b : Position d → Position d → Position d) : Point (N*d) → Point (N*d) :=
  equivDrift (configurationEuclidean d N) (particleDrift b)

/-- A finite value bound used only for existence, never in the Jacobian exponent. -/
def valueBound (d N : ℕ) (M : ℝ) (hM : 0 ≤ M) : ℝ≥0 :=
  NNReal.mk (‖(configurationEuclidean d N).toContinuousLinearMap‖*M) (mul_nonneg (norm_nonneg _) hM)

/-- The genuine particle-number-independent Euclidean Lipschitz bound. -/
def lipBound (d : ℕ) (L₁ L₂ : ℝ) : ℝ≥0 :=
  NNReal.mk (Real.sqrt (2*d*(L₁^2+L₂^2))) (Real.sqrt_nonneg _)

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}

theorem drift_norm_le (hN : 0 < N) (hbound : KernelBounds b M L₁ L₂) (hM : 0 ≤ M)
    (y : Point (N*d)) : ‖drift b y‖ ≤ valueBound d N M hM := by
  exact ((configurationEuclidean d N).toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (particleDrift_norm_bound hN hbound hM _) (norm_nonneg _))

theorem drift_lipschitz (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    LipschitzWith (lipBound d L₁ L₂) (drift (N := N) b) :=
  euclidean_particleDrift_lipschitz hN hb hbound hL₁ hL₂

theorem drift_smooth (hb : BoundedSmoothKernel b) : ContDiff ℝ ∞ (drift (N := N) b) :=
  equivDrift_smooth _ (particleDrift_smooth hb)

theorem drift_allDerivativesBounded (hb : BoundedSmoothKernel b) :
    AllDerivativesBounded (drift (N := N) b) :=
  equivDrift_allDerivativesBounded _ (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb)

theorem drift_locallyUniform (hN : 0 < N) (hb : BoundedSmoothKernel b)
    (hbound : KernelBounds b M L₁ L₂) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    TendstoLocallyUniformly (fun n => drift (N := N) (PeriodicParticle.interaction b n)) (drift b) atTop := by
  have hh := (PeriodicParticle.drift_locallyUniform hN hb hbound hL₁ hL₂).comp
    (configurationEuclidean d N).symm (configurationEuclidean d N).symm.continuous
  exact (configurationEuclidean d N).toContinuousLinearMap.uniformContinuous.comp_tendstoLocallyUniformly hh

theorem drift_fderiv_moving_tendsto (hb : BoundedSmoothKernel b)
    {x : ℕ → Point (N*d)} {y : Point (N*d)} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => fderiv ℝ (drift (N := N) (PeriodicParticle.interaction b n)) (x n))
      atTop (𝓝 (fderiv ℝ (drift b) y)) :=
  PeriodicParticle.euclidean_fderiv_particleDrift_moving_tendsto hb hx

/-- The actual selected continuous-input particle flow, in genuine Euclidean coordinates. -/
def flow (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
    (x : Point (N*d)) (w : C(Icc 0 T,Point (N*d))) (t : ℝ) : Point (N*d) :=
  autonomousFlow (drift_norm_le hN hbound hM) (drift_lipschitz hN hb hbound hL₁ hL₂) hT x w t

theorem flow_tendsto (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
    (x : Point (N*d)) (w : C(Icc 0 T,Point (N*d))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => flow hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT x w t)
      atTop (𝓝 (flow hN hb hbound hM hL₁ hL₂ hT x w t)) := by
  exact BoundedFlow.flow_drift_tendsto
    (u := fun n _ => drift (N := N) (PeriodicParticle.interaction b n)) (v := fun _ => drift b)
    (fun n => (drift_lipschitz hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hL₁ hL₂).continuous.comp continuous_snd)
    (fun n _ => drift_norm_le hN (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM)
    (fun n _ => drift_lipschitz hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hL₁ hL₂)
    ((drift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (fun _ => drift_norm_le hN hbound hM) (fun _ => drift_lipschitz hN hb hbound hL₁ hL₂) hT
    ((drift_locallyUniform hN hb hbound hL₁ hL₂).comp Prod.snd continuous_snd) x w ht

/-- Actual operator-norm convergence of the periodized particle-flow Jacobians. -/
theorem flow_fderiv_tendsto (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
    (x : Point (N*d)) (w : C(Icc 0 T,Point (N*d))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => fderiv ℝ (fun y => flow hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM hL₁ hL₂ hT y w t) x)
      atTop (𝓝 (fderiv ℝ (fun y => flow hN hb hbound hM hL₁ hL₂ hT y w t) x)) := by
  exact FlowJacobianDrift.fderiv_flow_tendsto_of_locallyUniform_boundedSmooth
    (fun n => drift_norm_le hN (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hM)
    (fun n => drift_lipschitz hN (PeriodicParticle.interaction_smooth hb n)
      (PeriodicParticle.interaction_bounds hb hbound hL₁ hL₂ n) hL₁ hL₂)
    (fun n => drift_smooth (PeriodicParticle.interaction_smooth hb n))
    (fun n => drift_allDerivativesBounded (PeriodicParticle.interaction_smooth hb n))
    (drift_norm_le hN hbound hM) (drift_lipschitz hN hb hbound hL₁ hL₂)
    (drift_smooth hb) (drift_allDerivativesBounded hb) hT w x
    (drift_locallyUniform hN hb hbound hL₁ hL₂) (fun _ _ => drift_fderiv_moving_tendsto hb) ht

/-- The actual norm bound has an exponent independent of the particle number. -/
theorem flow_fderiv_norm_le (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
    (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) {T : ℝ} (hT : 0 ≤ T)
    (x : Point (N*d)) (w : C(Icc 0 T,Point (N*d))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖fderiv ℝ (fun y => flow hN hb hbound hM hL₁ hL₂ hT y w t) x‖ ≤
      Real.exp ((lipBound d L₁ L₂:ℝ)*t) :=
  (autonomousFlow_hasFDerivAt_and_norm_of_boundedSmooth
    (drift_norm_le hN hbound hM) (drift_lipschitz hN hb hbound hL₁ hL₂)
    (drift_smooth hb) (drift_allDerivativesBounded hb) hT w x ht).2

end SharpWasserstein.PeriodicParticleTangentLimit
