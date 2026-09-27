import SharpWasserstein.BrownianPeriodicHierarchyProfile
import SharpWasserstein.BrownianSourceInitialFlux

/-! The sharp periodic propagated profile is initialized from one genuine
initial flux distribution and its actual marginal energies. This formulation
is independent of the particular kernel used for the later propagation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace NNReal
namespace SharpWasserstein.BrownianPeriodicHierarchy
open WeightedTangent PropagatedSourceEquation NoiseAverage PropagatedSourcePermutation

/-- A carrying-law equality preserves every actual full prefix source energy. -/
theorem levelEnergy_measure_congr {d N : ℕ} (ν τ : Measure (Point (N*d)))
    [IsFiniteMeasure ν] [IsFiniteMeasure τ] (h : ν = τ)
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (m : ℕ) :
    energy (levelLaw d N ν m) (levelSource d N ν σ m) =
    energy (levelLaw d N τ m) (levelSource d N τ σ m) := by
  subst τ
  rfl

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
/-- Kernel-independent initialization: the very same actual L² current and
its distribution are propagated, and all initial levels come from that one
full distribution. -/
theorem brownian_periodic_quadratic_bound_initial_flux
    {P : ℝ} (hP : 0 < P) (hN : 0 < N) (hex : Exchangeable μ)
    (hue : ∀ e : Equiv.Perm (Fin N),∀ᵐ x ∂μ.map (configurationEuclidean d N),
      u (euclideanPermutation e x)=euclideanPermutation e (u x))
    {Mb L₁ L₂ A : ℝ} (hbound : KernelBounds b Mb L₁ L₂)
    (hM : 0 ≤ Mb) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hA : 0 ≤ A)
    (hx : ∀ a x y,b (x+Pi.single a P) y=b x y)
    (hy : ∀ a x y,b x (y+Pi.single a P)=b x y)
    (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : ∀ φ : Test (N*d),σ₀ φ = ∫ x,⟪gradient φ.val x,u x⟫_ℝ ∂μ.map (configurationEuclidean d N))
    (hinit : ∀ m,1 ≤ m → m ≤ N →
      energy (levelLaw d N (μ.map (configurationEuclidean d N)) m)
        (levelSource d N (μ.map (configurationEuclidean d N)) σ₀ m) ≤
          A*(m:ℝ)^2/(N:ℝ)^2) :
    ∀ m,1 ≤ m → m ≤ N → ∀ t ∈ Icc 0 T,
      brownianPeriodicEnergy hv' hb' hl' hT hbs μ hu P m t ≤
        A*Real.exp (4*comparisonConstant d Mb L₁ L₂*t)*(m:ℝ)^2/(N:ℝ)^2 := by
  apply brownian_periodic_quadratic_bound hv hb hl hv' hb' hl' hT hbs μ hμ hu
    hP hN hex hue hbound hM hL₁ hL₂ hA hx hy
  intro m hm hmN
  dsimp only
  rw [Brownian.sourceAt_zero_of_divergence hv' hb' hl' hT
    (particleDrift_smooth hbs) (particleDrift_allDerivativesBounded hbs) _ hu σ₀ hσ₀]
  exact (levelEnergy_measure_congr _ _ (Brownian.lawAt_zero hv' hb' hl' hT _) σ₀ m).trans_le
    (hinit m hm hmN)

end SharpWasserstein.BrownianPeriodicHierarchy
