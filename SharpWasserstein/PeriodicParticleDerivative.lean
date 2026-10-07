module

public import SharpWasserstein.Compat
public import SharpWasserstein.SinePeriodizationDerivative
public import SharpWasserstein.PeriodicParticleApproximation
public import SharpWasserstein.ConfigurationEuclidean

@[expose] public section

/-! Genuine particle-drift Jacobian convergence for the actual smooth
periodization, including the Euclidean-coordinate version used by tangent
propagation. No convergence of Jacobians is postulated. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff
namespace SharpWasserstein.PeriodicParticle

def pairProjection {d N : ℕ} (i j : Fin N) :
    Configuration d N →L[ℝ] Position d × Position d :=
  (ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j)

def driftDerivative {d N : ℕ} (b : Position d → Position d → Position d)
    (x : Configuration d N) : Configuration d N →L[ℝ] Configuration d N :=
  ContinuousLinearMap.pi fun i : Fin N => (N : ℝ)⁻¹ • ∑ j : Fin N,
    (fderiv ℝ (Function.uncurry b) (x i,x j)).comp (pairProjection i j)

theorem particleDrift_hasFDerivAt {d N : ℕ} {b : Position d → Position d → Position d}
    (hb : ContDiff ℝ 1 (Function.uncurry b)) (x : Configuration d N) :
    HasFDerivAt (particleDrift b) (driftDerivative b x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  have h (j : Fin N) : HasFDerivAt (fun y : Configuration d N => b (y i) (y j))
      ((fderiv ℝ (Function.uncurry b) (x i,x j)).comp (pairProjection i j)) x :=
    ((hb.differentiable (by norm_num) _).hasFDerivAt.comp x (pairProjection i j).hasFDerivAt)
  convert (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => h j).const_smul (N : ℝ)⁻¹ using 1
  rfl

theorem fderiv_particleDrift {d N : ℕ} {b : Position d → Position d → Position d}
    (hb : ContDiff ℝ 1 (Function.uncurry b)) (x : Configuration d N) :
    fderiv ℝ (particleDrift b) x = driftDerivative b x :=
  (particleDrift_hasFDerivAt hb x).fderiv

/-- Along every converging sequence of configurations, the derivative of
the actual periodized particle drift converges in operator norm. -/
theorem driftDerivative_moving_tendsto {d N : ℕ} {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) {x : ℕ → Configuration d N} {y : Configuration d N}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k => driftDerivative (interaction b k) (x k)) atTop (𝓝 (driftDerivative b y)) := by
  have h (i j : Fin N) := SinePeriodization.fderiv_kernel_moving_tendsto
    (hb.smooth.of_le (by simp)) (tendsto_pi_nhds.mp hx i) (tendsto_pi_nhds.mp hx j)
  have hc (i j : Fin N) : Continuous (fun A : (Position d × Position d) →L[ℝ] Position d =>
      A.comp (pairProjection (d := d) i j)) := continuous_id.clm_comp continuous_const
  have hs (i : Fin N) := (tendsto_finsetSum Finset.univ
    (fun j _ => (hc i j).continuousAt.tendsto.comp (h i j))).const_smul (N : ℝ)⁻¹
  have hp := (ContinuousLinearMap.piEquivL ℝ (Configuration d N) (fun _ : Fin N => Position d)).continuous.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr hs)
  exact hp

theorem fderiv_particleDrift_moving_tendsto {d N : ℕ} {b : Position d → Position d → Position d}
    (hb : BoundedSmoothKernel b) {x : ℕ → Configuration d N} {y : Configuration d N}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k => fderiv ℝ (particleDrift (interaction b k)) (x k)) atTop
      (𝓝 (fderiv ℝ (particleDrift b) y)) := by
  simp_rw [fderiv_particleDrift ((interaction_smooth hb _).smooth.of_le (by simp)),
    fderiv_particleDrift (hb.smooth.of_le (by simp))]
  exact driftDerivative_moving_tendsto hb hx

theorem fderiv_linearConjugate {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F)
    {v : E → E} (hv : Differentiable ℝ v) (y : F) :
    fderiv ℝ (fun z => L (v (L.symm z))) y =
      L.toContinuousLinearMap.comp ((fderiv ℝ v (L.symm y)).comp L.symm.toContinuousLinearMap) :=
  ((L.hasFDerivAt).comp y ((hv _).hasFDerivAt.comp y L.symm.hasFDerivAt)).fderiv

/-- The derivative limit also holds in the genuine Euclidean configuration
operator norm; this is an exact coordinate change, not a norm identification. -/
theorem euclidean_fderiv_particleDrift_moving_tendsto {d N : ℕ}
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b)
    {x : ℕ → WeightedTangent.Point (N*d)} {y : WeightedTangent.Point (N*d)}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k => fderiv ℝ (fun z => configurationEuclidean d N
      (particleDrift (interaction b k) ((configurationEuclidean d N).symm z))) (x k)) atTop
      (𝓝 (fderiv ℝ (fun z => configurationEuclidean d N
        (particleDrift b ((configurationEuclidean d N).symm z))) y)) := by
  let L := configurationEuclidean d N
  have h := fderiv_particleDrift_moving_tendsto hb (L.symm.continuous.continuousAt.tendsto.comp hx)
  have hc : Continuous (fun A : Configuration d N →L[ℝ] Configuration d N =>
      L.toContinuousLinearMap.comp (A.comp L.symm.toContinuousLinearMap)) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have hh := hc.continuousAt.tendsto.comp h
  have hd : Differentiable ℝ (particleDrift (N := N) b) := fun z =>
    (particleDrift_hasFDerivAt (hb.smooth.of_le (by simp)) z).differentiableAt
  have hdk (k : ℕ) : Differentiable ℝ (particleDrift (N := N) (interaction b k)) := fun z =>
    (particleDrift_hasFDerivAt ((interaction_smooth hb k).smooth.of_le (by simp)) z).differentiableAt
  change Tendsto (fun k => fderiv ℝ (fun z => L (particleDrift (interaction b k) (L.symm z))) (x k))
    atTop (𝓝 (fderiv ℝ (fun z => L (particleDrift b (L.symm z))) y))
  simp_rw [fderiv_linearConjugate L hd,fderiv_linearConjugate L (hdk _)]
  exact hh

end SharpWasserstein.PeriodicParticle
