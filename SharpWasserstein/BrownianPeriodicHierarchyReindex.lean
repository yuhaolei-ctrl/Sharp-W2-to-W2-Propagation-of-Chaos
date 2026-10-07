module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionConsistency
public import SharpWasserstein.WeightedPeriodicTangentPhysical

@[expose] public section

/-! The next-particle observation has dimension m*d+d, while the genuine
(m+1)-particle prefix has dimension (m+1)*d. They differ only by arithmetic
coordinate reindexing. Laws, sources, and physical periodic energies agree. -/
noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace SharpWasserstein.BrownianPeriodicHierarchy
open WeightedTangent InitialSourceMarginal WeightedMarginal PeriodicParticleTangentLimit
open ExternalInteractionSymmetry PeriodicMarginalCoefficientEvolution

def coordinateCast {n k : ℕ} (h : n=k) : Point n ≃ₗᵢ[ℝ] Point k :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    { toFun := Fin.cast h
      invFun := Fin.cast h.symm
      left_inv := fun _ => by apply Fin.ext; rfl
      right_inv := fun _ => by apply Fin.ext; rfl }

theorem coordinateCast_rfl (n : ℕ) : coordinateCast (rfl : n=n) = LinearIsometryEquiv.refl ℝ (Point n) := by
  ext x i
  rfl

theorem imageSource_id {n : ℕ} (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    imageSource μ σ (ContinuousLinearMap.id ℝ (Point n)) = σ := by
  ext φ
  rw [imageSource_apply]
  change (∫ x,⟪gradient (φ.val ∘ id) x,(representative μ σ).val x⟫_ℝ ∂μ) = _
  simpa only [Function.comp_id] using (representative_divergence μ σ hσ φ).symm

theorem periodicEnergy_measure_congr {n : ℕ} (P : ℝ)
    (μ ν : Measure (Point n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ=ν) (σ : Test n →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangentPhysical.energy P μ σ = WeightedPeriodicTangentPhysical.energy P ν σ := by
  subst ν
  rfl

/-- Arithmetic coordinate transport leaves the actual periodic variational
energy unchanged. This is proved by equality transport, not by assuming
invariance under arbitrary linear maps. -/
theorem periodicEnergy_coordinateCast {n k : ℕ} (h : n=k) (P : ℝ)
    (μ : Measure (Point n)) [IsFiniteMeasure μ]
    (σ : Test n →ₗ[ℝ] ℝ) (hσ : FiniteEnergy μ σ) :
    WeightedPeriodicTangentPhysical.energy P (μ.map (coordinateCast h))
      (imageSource μ σ (coordinateCast h).toContinuousLinearEquiv.toContinuousLinearMap) =
      WeightedPeriodicTangentPhysical.energy P μ σ := by
  subst k
  rw [coordinateCast_rfl]
  change WeightedPeriodicTangentPhysical.energy P (μ.map id)
    (imageSource μ σ (ContinuousLinearMap.id ℝ (Point n))) = _
  rw [imageSource_id μ σ hσ]
  exact periodicEnergy_measure_congr P _ _ Measure.map_id σ

/-- The exact arithmetic reindexing of the genuine next prefix. -/
def nextCoordinates (d m : ℕ) : Point ((m+1)*d) ≃ₗᵢ[ℝ] Point (m*d+d) :=
  coordinateCast (by simp [Nat.add_mul])

theorem observation_eq_nextProjection {d m N : ℕ} (hm : m < N) :
    observation (d := d) hm.le ⟨m,hm⟩ =
      (nextCoordinates d m).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (marginalProjection (Nat.succ_le_of_lt hm)) := by
  ext x k
  obtain ⟨z,rfl⟩ := (configurationEuclidean d N).surjective x
  rw [ContinuousLinearMap.comp_apply,marginalProjection_coordinates]
  cases k using Fin.addCases with
  | left k =>
      obtain ⟨⟨i,a⟩,rfl⟩ := finProdFinEquiv.surjective k
      have hi : Fin.cast (by simp [Nat.add_mul] : m*d+d=(m+1)*d)
          ((finProdFinEquiv (i,a)).castAdd d) = finProdFinEquiv (Fin.castSucc i,a) := by
        apply Fin.ext
        rfl
      have ho := congrArg (fun y : Point (m*d) => y (finProdFinEquiv (i,a)))
        (observation_prefix hm.le ⟨m,hm⟩ z)
      change observation hm.le ⟨m,hm⟩ (configurationEuclidean d N z)
        ((finProdFinEquiv (i,a)).castAdd d) =
          configurationEuclidean d m (restrictCoordinates hm.le z) (finProdFinEquiv (i,a)) at ho
      rw [ho,configurationEuclidean_apply_coordinate]
      change z (Fin.castLE hm.le i) a =
          configurationEuclidean d (m+1) (restrictCoordinates (Nat.succ_le_of_lt hm) z)
            (Fin.cast (by simp [Nat.add_mul]) ((finProdFinEquiv (i,a)).castAdd d))
      rw [hi,configurationEuclidean_apply_coordinate]
      rfl
  | right a =>
      have hi : Fin.cast (by simp [Nat.add_mul] : m*d+d=(m+1)*d) (Fin.natAdd (m*d) a) =
          finProdFinEquiv (Fin.last m,a) := by
        apply Fin.ext
        change m*d+a.val=a.val+d*m
        ac_rfl
      have ho := congrArg (fun y : Position d => y a) (observation_external hm.le ⟨m,hm⟩ z)
      change observation hm.le ⟨m,hm⟩ (configurationEuclidean d N z) (Fin.natAdd (m*d) a) = z ⟨m,hm⟩ a at ho
      rw [ho]
      change z ⟨m,hm⟩ a =
        configurationEuclidean d (m+1) (restrictCoordinates (Nat.succ_le_of_lt hm) z)
          (Fin.cast (by simp [Nat.add_mul]) (Fin.natAdd (m*d) a))
      rw [hi,configurationEuclidean_apply_coordinate]
      rfl

/-- Literal law equality for the next-particle observation. -/
theorem observed_nextLaw {d m N : ℕ} (hm : m < N) (μ : Measure (Point (N*d))) :
    μ.map (observation (d := d) hm.le ⟨m,hm⟩) =
      (μ.map (marginalProjection (Nat.succ_le_of_lt hm))).map (nextCoordinates d m) := by
  rw [Measure.map_map (nextCoordinates d m).continuous.measurable
    (marginalProjection (Nat.succ_le_of_lt hm)).continuous.measurable,observation_eq_nextProjection]
  rfl

/-- Literal source equality, derived from actual successive marginalization. -/
theorem observed_nextSource {d m N : ℕ} (hm : m < N)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ) :
    observedSource hm.le ⟨m,hm⟩ μ (representative μ σ).val =
      imageSource (μ.map (marginalProjection (Nat.succ_le_of_lt hm)))
        (prefixSource (Nat.succ_le_of_lt hm) μ (representative μ σ).val)
        (nextCoordinates d m).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [observedSource_eq_imageSource,prefixSource_eq_imageSource,imageSource_comp,
    observation_eq_nextProjection]

/-- The external next-source energy is precisely the actual (m+1)-prefix
energy, with no dimension factor or independently selected marginal. -/
theorem observed_nextEnergy {d m N : ℕ} (hm : m < N) (P : ℝ)
    (μ : Measure (Point (N*d))) [IsFiniteMeasure μ] (σ : Test (N*d) →ₗ[ℝ] ℝ) :
    WeightedPeriodicTangentPhysical.energy P (μ.map (observation hm.le ⟨m,hm⟩))
      (observedSource hm.le ⟨m,hm⟩ μ (representative μ σ).val) =
      WeightedPeriodicTangentPhysical.energy P (μ.map (marginalProjection (Nat.succ_le_of_lt hm)))
        (prefixSource (Nat.succ_le_of_lt hm) μ (representative μ σ).val) := by
  rw [observed_nextSource]
  exact (periodicEnergy_measure_congr P _ _ (observed_nextLaw hm μ) _).trans
    (periodicEnergy_coordinateCast _ P _ _ (prefixSource_finiteEnergy _ _ _))

end SharpWasserstein.BrownianPeriodicHierarchy
