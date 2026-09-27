import SharpWasserstein.BrownianPeriodicHierarchyEstimate
import SharpWasserstein.VolterraFourierSourceHierarchy

/-! Sharp quadratic periodic marginal source profile for the actual Brownian
law and actual propagated current. The finite trial differential inequalities,
scalar recovery, and positive-kernel hierarchy comparison are all proved; no
limiting-energy derivative or limiting hierarchy is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.BrownianPeriodicHierarchy
open WeightedTangent PropagatedSourceEquation NoiseAverage PropagatedSourcePermutation
open VolterraFourier

variable {d N : ℕ} {b : Position d → Position d → Position d} {M K M' K' : ℝ≥0}
  (hv : Continuous (Function.uncurry (fun _ : ℝ => (particleDrift b : Configuration d N → _))))
  (hb : ∀ _ : ℝ,∀ x : Configuration d N,‖particleDrift b x‖ ≤ M)
  (hl : ∀ _ : ℝ,LipschitzWith K (particleDrift b : Configuration d N → _))
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) (particleDrift b))))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) (particleDrift b) y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) (particleDrift b)))
  {T : ℝ} (hT : 0 ≤ T) (hbs : BoundedSmoothKernel b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ] (hμ : HasSecondMoment μ)
  {u : Point (N*d) → Point (N*d)} (hu : MemLp u 2 (μ.map (configurationEuclidean d N)))



include hv hb hl hμ in
/-- The actual periodic propagated profile, with constants independent of
particle number, Fourier scale, time horizon, and auxiliary higher derivatives. -/
theorem brownian_periodic_quadratic_bound {P : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x)=euclideanPermutation e (u x))
    {Mb L₁ L₂ A : ℝ} (hbound : KernelBounds b Mb L₁ L₂)
    (hM : 0 ≤ Mb) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hA : 0 ≤ A)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (hinit : ∀ m,1 ≤ m → m ≤ N →
      let ν := Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) 0
      let σ := Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
        (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu 0
      WeightedTangent.energy (levelLaw d N ν m) (levelSource d N ν σ m) ≤
        A*(m:ℝ)^2/(N:ℝ)^2) :
    ∀ m,1 ≤ m → m ≤ N → ∀ t ∈ Icc 0 T,
      brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P m t ≤
        A*Real.exp (4*comparisonConstant d Mb L₁ L₂*t)*(m:ℝ)^2/(N:ℝ)^2 := by
  let ν := fun r => Brownian.lawAt hv' hb' hl' hT (μ.map (configurationEuclidean d N)) r
  let σ := fun r => Brownian.sourceAt hv' hb' hl' hT (particleDrift_smooth hbs)
    (particleDrift_allDerivativesBounded hbs) (μ.map (configurationEuclidean d N)) u hu r
  let B := Real.exp ((K':ℝ)*T)^2*(∫ x,‖u x‖^2 ∂(μ.map (configurationEuclidean d N)))
  have hh := source_quadratic_bound_of_finite_derivatives P
    (fun m r => levelLaw d N (ν r) m) (fun m r => levelSource d N (ν r) (σ r) m)
    hN hA (comparisonConstant_nonneg d Mb L₁ L₂) hT
    (fun _ => baseline d L₁ L₂) (rate d Mb L₁ L₂ N) (gapCoefficient N hbs L₁ L₂)
    (fun _ _ _ => baseline_le_comparison d Mb L₁ L₂)
    (fun m _ hm => (rate_bounds d Mb L₁ L₂ hN hm.le).1)
    (fun m _ hm => (rate_bounds d Mb L₁ L₂ hN hm.le).2)
    (fun _ _ _ _ _ => levelSource_finite _ _ _ _ _)
    (fun m _ hm j => brownianFiniteEnergy_continuousOn hv hb hl hv' hb' hl' hT hbs μ hμ hu hP hm j)
    (f' := fun m j => deriv (brownianFiniteEnergy hv' hb' hl' hT hbs μ hu P m j))
    (fun m _ hm j r hr => brownianFiniteEnergy_hasDerivAt hv hb hl hv' hb' hl' hT hbs μ hμ hu hP hm j hr)
    (B := fun _ _ => B) (fun _ _ _ => intervalIntegrable_const)
    (fun m _ _ r hr => (brownian_level_energy_bound_flux hv' hb' hl' hT
      (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs)
      (μ.map (configurationEuclidean d N)) u hu m hr).2)
    (fun m hmpos hm j r hr => brownianFiniteEnergy_deriv_le hv hb hl hv' hb' hl' hT hbs μ hμ hu
      hP hm hmpos hex hue hbound hM hL₁ hL₂ hx hy j hr)
    (fun j r hr => brownianFiniteEnergy_terminal_deriv_le hv hb hl hv' hb' hl' hT hbs μ hμ hu
      hP hN hbound hL₁ hL₂ hx hy j hr)
    hinit
  intro m hm hmN t ht
  have h := hh m hm hmN t ht
  simp only [sub_zero] at h
  convert h using 1
  rfl

end SharpWasserstein.BrownianPeriodicHierarchy
