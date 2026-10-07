module

public import SharpWasserstein.Compat
public import SharpWasserstein.RegularizedTrialConvergencePeriodic
public import SharpWasserstein.FiniteGradientTrial
public import SharpWasserstein.WeightedPeriodicFourierPhysical

@[expose] public section

/-! Recovery by coefficient-regularized Fourier trials at their genuine
physical period. The carrying measure and physical Euclidean weighted norm
are unchanged; the test potential is evaluated at the scaled coordinate. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace
namespace SharpWasserstein.RegularizedTrialConvergencePhysical
open WeightedTangent PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicSmoothGradient (SmoothPeriodicTest)
open WeightedPeriodicFourierPhysical RegularizedTrialConvergence RegularizedTrialConvergencePeriodic

variable {n : ℕ} [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (P : ℝ) (μ : Measure (Point n)) [IsFiniteMeasure μ]

def atomVector (p : (Fin n → ℤ) × Bool) : Lp (Point n) 2 μ :=
  (WeightedPeriodicFourierPhysical.gradientVector P μ (atom p) (smooth_atom p) (periodic_atom p)).val

/-- The actual physical periodic closure embeds in the closed span of the
physical atom gradients, without a density or coefficient-recovery premise. -/
theorem periodic_mem_atomClosure {U : gradientClosure μ}
    (hU : U ∈ WeightedPeriodicFourierPhysical.periodicSpace P μ) :
    U.val ∈ (Submodule.span ℝ (Set.range (atomVector P μ))).topologicalClosure := by
  let S := (Submodule.span ℝ (Set.range (atomVector P μ))).topologicalClosure
  let L := (gradientClosure μ).subtype.comp (WeightedPeriodicFourierPhysical.periodicGradientMap P μ)
  have hle : WeightedPeriodicFourierPhysical.periodicSpace P μ ≤
      S.comap (gradientClosure μ).subtype := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro s V hV
      obtain ⟨f,rfl⟩ := hV
      change (WeightedPeriodicFourierPhysical.gradientVector P μ f.val
        (frequencySpace_properties s f.property).1
        (frequencySpace_properties s f.property).2.1).val ∈ S
      apply (Submodule.span ℝ (Set.range (atomVector P μ))).le_topologicalClosure
      exact frequency_image_mem_span L f.property
        (frequencySpace_properties s f.property).1 (frequencySpace_properties s f.property).2.1
    · exact (Submodule.span ℝ (Set.range (atomVector P μ))).isClosed_topologicalClosure.preimage
        (gradientClosure μ).subtypeL.continuous
  exact hle hU

/-- The literal finite weighted gradient operator of physical Fourier tests. -/
def trial (s : Finset ((Fin n → ℤ) × Bool)) : EuclideanSpace ℝ s →L[ℝ] Lp (Point n) 2 μ :=
  FiniteGradientTrial.gradientMap μ (fun p : s => physicalPotential P (atom p.val))
    (fun p => physicalPotential_smooth P (smooth_atom p.val))
    (fun p => physicalPotential_gradient_bound P (atom p.val) (smooth_atom p.val) (periodic_atom p.val))

theorem trial_eq_synthesis (s : Finset ((Fin n → ℤ) × Bool)) :
    trial P μ s = synthesis (atomVector P μ) s := by
  apply ContinuousLinearMap.ext
  intro c
  rw [trial,FiniteGradientTrial.gradientMap_apply,synthesis_apply]
  apply Finset.sum_congr rfl
  intro p _
  rfl

/-- The regularized actual physical Fourier energies converge to the norm of
every vector in the independently constructed physical periodic closure. -/
theorem energy_tendsto {J : Type*} {l : Filter J}
    (s : J → Finset ((Fin n → ℤ) × Bool)) (δ : J → ℝ)
    (hs : ∀ p,∀ᶠ j in l,p ∈ s j) (hδpos : ∀ j,0 < δ j)
    (hδ : Tendsto δ l (𝓝 0)) (U : gradientClosure μ)
    (hU : U ∈ WeightedPeriodicFourierPhysical.periodicSpace P μ) :
    Tendsto (fun j => RegularizedTrialEnergy.energy (trial P μ (s j)) (δ j) U.val)
      l (𝓝 (‖U‖^2)) := by
  simpa only [trial_eq_synthesis,Submodule.norm_coe] using
    RegularizedTrialConvergence.energy_tendsto (atomVector P μ) s δ hs hδpos hδ U.val
      (periodic_mem_atomClosure P μ hU)

end SharpWasserstein.RegularizedTrialConvergencePhysical
