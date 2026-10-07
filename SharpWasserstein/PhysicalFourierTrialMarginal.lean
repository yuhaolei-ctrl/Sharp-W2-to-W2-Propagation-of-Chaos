module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedTrialMarginal
public import SharpWasserstein.RegularizedTrialConvergencePhysical
public import SharpWasserstein.WeightedPeriodicMarginalPhysical

@[expose] public section

/-! The actual next-marginal fluctuation of a finite physical Fourier
optimizer equals next-level periodic energy minus its regularized trial
energy and coefficient penalty. No marginal pairing is an assumption. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff InnerProductSpace BigOperators
namespace SharpWasserstein.PhysicalFourierTrialMarginal
open WeightedTangent WeightedMarginal PeriodicFourierTests
open WeightedPeriodicFourierPhysical RegularizedTrialConvergencePhysical
variable {n m : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  [MeasurableSpace (Point (n+m))] [BorelSpace (Point (n+m))]
  (P : ℝ) (μ : Measure (Point (n+m))) [IsFiniteMeasure μ]

omit [BorelSpace (Point (n+m))] in
/-- Every literal finite trial vector lies in the proved physical periodic
closure, even for a singular marginal probability. -/
theorem trial_mem_periodic (s : Finset ((Fin n → ℤ) × Bool)) (c : EuclideanSpace ℝ s) :
    ∃ w : periodicSpace P (marginalLaw μ), w.val.val = trial P (marginalLaw μ) s c := by
  let g : gradientClosure (marginalLaw μ) := ∑ p : s,c p •
    gradientVector P (marginalLaw μ) (atom p.val) (smooth_atom p.val) (periodic_atom p.val)
  have hg : g ∈ periodicSpace P (marginalLaw μ) := by
    apply Submodule.sum_mem
    intro p _
    exact Submodule.smul_mem _ _ (gradientVector_mem_periodicSpace P (marginalLaw μ)
      _ (smooth_atom p.val) (periodic_atom p.val))
  refine ⟨⟨g,hg⟩,?_⟩
  rw [trial,FiniteGradientTrial.gradientMap_apply]
  change ((∑ p : s,c p • gradientVector P (marginalLaw μ) (atom p.val)
    (smooth_atom p.val) (periodic_atom p.val) : gradientClosure (marginalLaw μ)) :
      Lp (Point n) 2 (marginalLaw μ)) = _
  simp only [Submodule.coe_sum,Submodule.coe_smul]
  rfl

/-- Actual canonical periodic marginalization supplies the precise pairing
needed by the coefficient optimizer's fluctuation calculation. -/
theorem trial_representative_pairing (σ : Test (n+m) →ₗ[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) (c : EuclideanSpace ℝ s) :
    ⟪(WeightedPeriodicTangentPhysical.representative P μ σ).val.val,
      vectorLift μ (trial P (marginalLaw μ) s c)⟫_ℝ =
    ⟪(WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
      (marginalDistribution μ σ)).val.val,trial P (marginalLaw μ) s c⟫_ℝ := by
  obtain ⟨w,hw⟩ := trial_mem_periodic P μ s c
  have hp := WeightedPeriodicMarginalPhysical.marginal_representative_pairing P μ σ w
  change ⟪(WeightedPeriodicTangentPhysical.representative P μ σ).val.val,vectorLift μ w.val.val⟫_ℝ =
    ⟪(WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
      (marginalDistribution μ σ)).val.val,w.val.val⟫_ℝ at hp
  rwa [hw] at hp

/-- The exact finite-trial next-level energy difference, including its
favourable coefficient penalty. -/
theorem trial_fluctuation_norm_sq (σ : Test (n+m) →ₗ[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ) :
    let T := trial P (marginalLaw μ) s
    let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
      (marginalDistribution μ σ)).val.val
    let c := RegularizedTrialEnergy.solution T δ U
    ‖(WeightedPeriodicTangentPhysical.representative P μ σ).val.val-vectorLift μ (T c)‖^2 =
      WeightedPeriodicTangentPhysical.energy P μ σ-RegularizedTrialEnergy.energy T δ U-δ*‖c‖^2 := by
  dsimp only
  rw [WeightedPeriodicTangentPhysical.energy_eq_norm_sq]
  exact RegularizedTrialEnergy.lifted_energy_gap _ (vectorLift μ) _ _ δ hδ
    (trial_representative_pairing P μ σ s)

/-- Literal Euclidean fluctuation integral for the same finite optimizer. -/
theorem trial_fluctuation_integral (σ : Test (n+m) →ₗ[ℝ] ℝ)
    (s : Finset ((Fin n → ℤ) × Bool)) {δ : ℝ} (hδ : 0 < δ) :
    let T := trial P (marginalLaw μ) s
    let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
      (marginalDistribution μ σ)).val.val
    let c := RegularizedTrialEnergy.solution T δ U
    let f := FiniteGradientTrial.potential (fun p : s => physicalPotential P (atom p.val)) c
    (∫ x,‖(WeightedPeriodicTangentPhysical.representative P μ σ).val.val x-
      prefixEmbedding n m (gradient f (prefixProjection n m x))‖^2 ∂μ) =
      WeightedPeriodicTangentPhysical.energy P μ σ-RegularizedTrialEnergy.energy T δ U-δ*‖c‖^2 := by
  dsimp only
  let T := trial P (marginalLaw μ) s
  let U := (WeightedPeriodicTangentPhysical.representative P (marginalLaw μ)
    (marginalDistribution μ σ)).val.val
  let c := RegularizedTrialEnergy.solution T δ U
  let V := (WeightedPeriodicTangentPhysical.representative P μ σ).val.val
  have he := trial_fluctuation_norm_sq P μ σ s hδ
  have hg := FiniteGradientTrial.gradientMap_ae (marginalLaw μ)
    (fun p : s => physicalPotential P (atom p.val))
    (fun p => physicalPotential_smooth P (smooth_atom p.val))
    (fun p => physicalPotential_gradient_bound P (atom p.val) (smooth_atom p.val) (periodic_atom p.val)) c
  have hgp := ae_of_ae_map (prefixProjection n m).continuous.measurable.aemeasurable hg
  have hi : ‖V-vectorLift μ (T c)‖^2 =
      ∫ x,‖V x-prefixEmbedding n m (gradient
        (FiniteGradientTrial.potential (fun p : s => physicalPotential P (atom p.val)) c)
          (prefixProjection n m x))‖^2 ∂μ := by
    rw [lp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub V (vectorLift μ (T c)),vectorLiftLinear_ae μ (T c),hgp] with x hx hy hz
    rw [hx,Pi.sub_apply]
    change ‖V x-vectorLiftLinear μ (T c) x‖^2 = _
    rw [hy]
    change ‖V x-prefixEmbedding n m (FiniteGradientTrial.gradientMap (marginalLaw μ) _ _ _ c
      (prefixProjection n m x))‖^2 = _
    rw [hz]
  change ‖V-vectorLift μ (T c)‖^2 = _ at he
  rw [hi] at he
  exact he

end SharpWasserstein.PhysicalFourierTrialMarginal
