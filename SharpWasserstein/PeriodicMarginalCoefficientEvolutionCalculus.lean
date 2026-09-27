import SharpWasserstein.PeriodicParticleTangentLimitMarginal
import SharpWasserstein.ExternalInteractionPeriodicSource
import SharpWasserstein.CylinderWeakEvolution
import SharpWasserstein.FiniteGeneratorBounds

/-! Literal cylinder calculus for particle marginals. The normalization uses
full N, includes diagonal interactions, and leaves the external sum explicit.
These are identities of the actual generator, with no marginal PDE premise. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.PeriodicMarginalCoefficientEvolution
open WeightedTangent PeriodicParticleTangentLimit ExternalInteractionSymmetry
open ExternalInteractionPeriodic PDEPairings PropagatedSourceEquation

variable {d m N : ℕ}

/-- A marginal observable is the genuine coordinate cylinder. -/
def cylinder (hm : m ≤ N) (f : Point (m*d) → ℝ) : Point (N*d) → ℝ :=
  f ∘ marginalProjection hm

@[simp] theorem cylinder_coordinates (hm : m ≤ N) (f : Point (m*d) → ℝ)
    (x : Configuration d N) :
    cylinder hm f (configurationEuclidean d N x) =
      f (configurationEuclidean d m (restrictCoordinates hm x)) := by
  simp only [cylinder,Function.comp_apply,marginalProjection_coordinates]

theorem cylinder_smooth (hm : m ≤ N) {f : Point (m*d) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cylinder hm f) := hf.comp (marginalProjection hm).contDiff

theorem cylinder_allDerivativesBounded (hm : m ≤ N) {f : Point (m*d) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : NoiseAverage.AllDerivativesBounded f) :
    NoiseAverage.AllDerivativesBounded (cylinder hm f) :=
  hB.comp_linear hf (marginalProjection hm)

@[simp] theorem marginalProjection_single_left {q : ℕ} (hm : m ≤ m+q)
    (i : Fin m) (a : Fin d) :
    marginalProjection (d := d) hm
      (EuclideanSpace.single (finProdFinEquiv (i.castAdd q,a)) 1) =
      EuclideanSpace.single (finProdFinEquiv (i,a)) 1 := by
  rw [← configurationEuclidean_coordinateVector, marginalProjection_coordinates,
    ← configurationEuclidean_coordinateVector]
  congr 1
  ext j c
  simp [restrictCoordinates,coordinateVector,Fin.ext_iff]

@[simp] theorem marginalProjection_single_right {q : ℕ} (hm : m ≤ m+q)
    (i : Fin q) (a : Fin d) :
    marginalProjection (d := d) hm
      (EuclideanSpace.single (finProdFinEquiv (i.natAdd m,a)) 1) = 0 := by
  rw [← configurationEuclidean_coordinateVector,marginalProjection_coordinates]
  have he : restrictCoordinates (d := d) hm (coordinateVector (i.natAdd m) a) = 0 := by
    ext j c
    have hji : Fin.castLE hm j ≠ i.natAdd m := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castLE,Fin.val_natAdd] at hv
      omega
    simp [restrictCoordinates,coordinateVector,hji]
  rw [he,map_zero]

/-- The full Euclidean diffusion acts on a cylinder as the true marginal
Laplacian, without a dimension factor. -/
theorem laplacian_cylinder (hm : m ≤ N) {f : Point (m*d) → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Point (N*d)) :
    PDEPairings.laplacian (cylinder hm f) x =
      PDEPairings.laplacian f (marginalProjection hm x) := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hm
  unfold PDEPairings.laplacian
  simp_rw [cylinder,CylinderWeakEvolution.directionDeriv_twice_comp_linear _ hf]
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type,Fin.sum_univ_add]
  simp only [marginalProjection_single_left,marginalProjection_single_right,
    directionDeriv,map_zero,Finset.sum_const_zero,add_zero]
  let g := fun k : Fin (m*d) => fderiv ℝ (directionDeriv (EuclideanSpace.single k 1) f)
    (marginalProjection hm x) (EuclideanSpace.single k 1)
  change (∑ i,∑ a,g (finProdFinEquiv (i,a))) = ∑ k,g k
  exact (Fintype.sum_prod_type _).symm.trans (Equiv.sum_comp finProdFinEquiv g)

/-- The drift part uses precisely the restricted full particle velocity. -/
theorem generator_cylinder (hm : m ≤ N) {f : Point (m*d) → ℝ}
    (hf : ContDiff ℝ 2 f) (v : Configuration d N → Configuration d N)
    (x : Point (N*d)) :
    euclideanGenerator v (cylinder hm f) x =
      PDEPairings.laplacian f (marginalProjection hm x) +
        fderiv ℝ f (marginalProjection hm x)
          (marginalProjection hm (equivDrift (configurationEuclidean d N) v x)) := by
  rw [FiniteGeneratorCalculus.euclideanGenerator_eq,FiniteGeneratorCalculus.generator_eq]
  dsimp only
  rw [laplacian_cylinder hm hf]
  unfold cylinder
  rw [fderiv_comp x ((hf.differentiable (by simp)) _) (marginalProjection hm).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

/-- Split a finite particle sum into the retained prefix and the genuine
external labels. This also covers the terminal marginal m=N. -/
theorem sum_prefix_external (hm : m ≤ N) (F : Fin N → ℝ) :
    (∑ j : Fin N,F j) = (∑ j : Fin m,F (Fin.castLE hm j)) +
      ∑ j : Fin N with m ≤ j.val,F j := by
  classical
  have hprefix : (∑ j : Fin N with j.val < m,F j) = ∑ j : Fin m,F (Fin.castLE hm j) := by
    symm
    apply Finset.sum_bij (fun j _ => Fin.castLE hm j)
    · intro j hj
      simp
    · intro i hi j hj hij
      exact Fin.castLE_injective hm hij
    · intro j hj
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj
      exact ⟨⟨j.val,hj⟩,Finset.mem_univ _,rfl⟩
    · intro j hj
      rfl
  rw [← hprefix,← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => j.val < m)]
  simp only [not_lt]

/-- The projected particle velocity is exactly the internal mean-field
velocity plus the sum of genuine external forces. -/
theorem projected_particleDrift (hm : m ≤ N)
    (b : Position d → Position d → Position d) (x : Point (N*d)) :
    marginalProjection hm (equivDrift (configurationEuclidean d N) (particleDrift b) x) =
      internalDrift N b (marginalProjection hm x) +
        (N:ℝ)⁻¹ • ∑ j : Fin N with m ≤ j.val,ExternalInteraction.force b (observation hm j x) := by
  classical
  obtain ⟨z,rfl⟩ := (configurationEuclidean d N).surjective x
  simp only [equivDrift,ContinuousLinearEquiv.symm_apply_apply,marginalProjection_coordinates]
  ext k
  obtain ⟨⟨i,a⟩,rfl⟩ := finProdFinEquiv.surjective k
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,WithLp.ofLp_sum,
    configurationEuclidean_apply_coordinate,restrictCoordinates,particleDrift,
    Pi.smul_apply,Finset.sum_apply]
  have hi := sum_prefix_external hm (fun j => b (z (Fin.castLE hm i)) (z j) a)
  rw [hi,mul_add]
  congr 1
  · simp [internalDrift,configurationEuclidean_apply_coordinate,restrictCoordinates]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp [ExternalInteraction.force,observation_positions,observation_external,
      configurationEuclidean_apply_coordinate,restrictCoordinates]

/-- Exact particle generator split on an actual cylinder potential: marginal
diffusion, internal interaction including self-terms, and external interactions. -/
theorem particle_generator_cylinder (hm : m ≤ N)
    (b : Position d → Position d → Position d) {f : Point (m*d) → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Point (N*d)) :
    euclideanGenerator (particleDrift b) (cylinder hm f) x =
      cylinder hm (fun y => PDEPairings.laplacian f y +
        ⟪internalDrift N b y,gradient f y⟫_ℝ) x +
      (N:ℝ)⁻¹ * ∑ j : Fin N with m ≤ j.val,particleInteraction hm j b f x := by
  classical
  rw [generator_cylinder hm hf,projected_particleDrift hm b]
  simp only [map_add,map_smul,map_sum,smul_eq_mul]
  rw [← inner_gradient_left,real_inner_comm]
  have he (j : Fin N) :
      (fderiv ℝ f (marginalProjection hm x)) (ExternalInteraction.force b (observation hm j x)) =
        particleInteraction hm j b f x := by
    rw [← inner_gradient_left,real_inner_comm]
    unfold particleInteraction ExternalInteraction.interaction
    congr 1
    obtain ⟨z,rfl⟩ := (configurationEuclidean d N).surjective x
    rw [observation_prefix,marginalProjection_coordinates]
  simp_rw [he]
  exact (add_assoc _ _ _).symm

end SharpWasserstein.PeriodicMarginalCoefficientEvolution
