module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicMarginalCoefficientEvolutionConsistency
public import SharpWasserstein.PropagatedSourceEquationDistribution

@[expose] public section

/-! A single full carrying law and source determine every level of the true
particle hierarchy. Levels beyond N are harmless zero observations, allowing
one total family of dimensions m*d; all valid levels are literal prefixes.
Canonical source contraction gives a uniform coarse Brownian energy bound. -/
noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff NNReal
namespace SharpWasserstein.BrownianPeriodicHierarchy
open WeightedTangent InitialSourceMarginal PeriodicParticleTangentLimit
open PeriodicMarginalCoefficientEvolution PropagatedSourceEquation NoiseAverage

def levelProjection (d N m : ℕ) : Point (N*d) →L[ℝ] Point (m*d) :=
  if hm : m ≤ N then marginalProjection hm else 0

theorem levelProjection_eq {d N m : ℕ} (hm : m ≤ N) :
    levelProjection d N m = marginalProjection hm := dif_pos hm

theorem levelProjection_norm_le_one (d N m : ℕ) : ‖levelProjection d N m‖ ≤ 1 := by
  unfold levelProjection
  split_ifs with hm
  · exact marginalProjection_norm_le_one hm
  · simp

def levelLaw (d N : ℕ) (ν : Measure (Point (N*d))) (m : ℕ) : Measure (Point (m*d)) :=
  ν.map (levelProjection d N m)

instance levelLaw_finite (d N : ℕ) (ν : Measure (Point (N*d))) [IsFiniteMeasure ν] (m : ℕ) :
    IsFiniteMeasure (levelLaw d N ν m) := Measure.isFiniteMeasure_map _ _

def levelSource (d N : ℕ) (ν : Measure (Point (N*d))) [IsFiniteMeasure ν]
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (m : ℕ) : Test (m*d) →ₗ[ℝ] ℝ :=
  imageSource ν σ (levelProjection d N m)

theorem levelLaw_eq {d N m : ℕ} (hm : m ≤ N) (ν : Measure (Point (N*d))) :
    levelLaw d N ν m = ν.map (marginalProjection hm) := by
  rw [levelLaw,levelProjection_eq hm]

theorem levelSource_eq {d N m : ℕ} (hm : m ≤ N)
    (ν : Measure (Point (N*d))) [IsFiniteMeasure ν] (σ : Test (N*d) →ₗ[ℝ] ℝ) :
    levelSource d N ν σ m = prefixSource hm ν (representative ν σ).val := by
  rw [levelSource,levelProjection_eq hm,prefixSource_eq_imageSource]

theorem levelSource_finite (d N : ℕ) (ν : Measure (Point (N*d))) [IsFiniteMeasure ν]
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (m : ℕ) : FiniteEnergy (levelLaw d N ν m) (levelSource d N ν σ m) :=
  imageSource_finite _ _ _

set_option maxHeartbeats 800000 in
/-- Every contracting genuine observation contracts the full source energy. -/
theorem imageSource_energy_le {n k : ℕ} (ν : Measure (Point n)) [IsFiniteMeasure ν]
    (σ : Test n →ₗ[ℝ] ℝ) (hσ : FiniteEnergy ν σ) (A : Point n →L[ℝ] Point k)
    (hA : ‖A‖ ≤ 1) : energy (ν.map A) (imageSource ν σ A) ≤ energy ν σ := by
  let U : Lp (Point n) 2 ν := (representative ν σ).val
  let V : Lp (Point k) 2 ν := A.compLpₗ 2 ν U
  have hiU : Integrable (fun x => ‖U x‖^2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp U).aestronglyMeasurable).mp (Lp.memLp U)
  have hiV : Integrable (fun x => ‖V x‖^2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp V).aestronglyMeasurable).mp (Lp.memLp V)
  calc
    _ ≤ ∫ x,‖V x‖^2 ∂ν := PropagatedFlux.source_energy_le _ _ _ V
    _ ≤ ∫ x,‖U x‖^2 ∂ν := by
      apply integral_mono_ae hiV hiU
      filter_upwards [A.coeFn_compLp U] with x hx
      change ‖A.compLp U x‖^2 ≤ ‖U x‖^2
      rw [hx]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      exact (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
    _ = _ := (energy_eq_integral ν σ hσ).symm

theorem levelSource_energy_le (d N : ℕ) (ν : Measure (Point (N*d))) [IsFiniteMeasure ν]
    (σ : Test (N*d) →ₗ[ℝ] ℝ) (hσ : FiniteEnergy ν σ) (m : ℕ) :
    energy (levelLaw d N ν m) (levelSource d N ν σ m) ≤ energy ν σ :=
  imageSource_energy_le ν σ hσ _ (levelProjection_norm_le_one d N m)

variable {d N : ℕ} {b : Configuration d N → Configuration d N} {M' K' : ℝ≥0}
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (ν₀ : Measure (Point (N*d))) [IsFiniteMeasure ν₀]

/-- All actual Brownian marginal source energies have one finite constant
bound on the whole horizon. The initial field is the genuine canonical Riesz
tangent, so no source-field measurability hypothesis is added. -/
theorem brownian_level_energy_bound (σ₀ : Test (N*d) →ₗ[ℝ] ℝ)
    (hσ₀ : FiniteEnergy ν₀ σ₀) (m : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := Brownian.lawAt hv' hb' hl' hT ν₀ t
    let σ := Brownian.distributionAt hv' hb' hl' hT hbs hB ν₀ σ₀ t
    FiniteEnergy (levelLaw d N ν m) (levelSource d N ν σ m) ∧
      energy (levelLaw d N ν m) (levelSource d N ν σ m) ≤
        Real.exp ((K':ℝ)*T)^2*energy ν₀ σ₀ := by
  dsimp only
  have hh := Brownian.distributionAt_finiteEnergy_and_energy_le hv' hb' hl' hT hbs hB ν₀ σ₀ hσ₀ ht
  refine ⟨levelSource_finite _ _ _ _ _,(levelSource_energy_le d N _ _ hh.1 m).trans (hh.2.trans ?_)⟩
  have he : Real.exp ((K':ℝ)*t) ≤ Real.exp ((K':ℝ)*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K'.coe_nonneg)
  apply mul_le_mul_of_nonneg_right ((sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr he)
  rw [energy_eq_norm_sq ν₀ σ₀ hσ₀]
  positivity

/-- Uniform domination for the actual propagated initial current. This bound
uses only its genuine L² norm; the sharp initial source profile is separate. -/
theorem brownian_level_energy_bound_flux (u : Point (N*d) → Point (N*d))
    (hu : MemLp u 2 ν₀) (m : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    let ν := Brownian.lawAt hv' hb' hl' hT ν₀ t
    let σ := Brownian.sourceAt hv' hb' hl' hT hbs hB ν₀ u hu t
    FiniteEnergy (levelLaw d N ν m) (levelSource d N ν σ m) ∧
      energy (levelLaw d N ν m) (levelSource d N ν σ m) ≤
        Real.exp ((K':ℝ)*T)^2*(∫ x,‖u x‖^2 ∂ν₀) := by
  dsimp only
  have hh := Brownian.sourceAt_finiteEnergy_and_energy_le hv' hb' hl' hT hbs hB ν₀ u hu ht
  refine ⟨levelSource_finite _ _ _ _ _,(levelSource_energy_le d N _ _ hh.1 m).trans (hh.2.trans ?_)⟩
  have he : Real.exp ((K':ℝ)*t) ≤ Real.exp ((K':ℝ)*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K'.coe_nonneg)
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr he)
    (integral_nonneg (fun _ => sq_nonneg _))

end SharpWasserstein.BrownianPeriodicHierarchy
