import SharpWasserstein.VolterraFourierHierarchy
import SharpWasserstein.WeightedPeriodicTangentPhysical

/-! The Fourier recovery interface specialized to the actual periodic
representative of a finite-energy distribution. Physical periodic membership
is automatic, and a coarse full source-energy bound controls all finite trial
gaps without any measurable choice of optimizer fields. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace SharpWasserstein.VolterraFourier
open WeightedTangent
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
  [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (P : ℝ) (μ : Ω → Measure (Point n)) [∀ t,IsFiniteMeasure (μ t)]
  (σ : Ω → (Test n →ₗ[ℝ] ℝ))

/-- The actual periodic projection of the canonical full weighted tangent. -/
def sourceRepresentative (t : Ω) : gradientClosure (μ t) :=
  (WeightedPeriodicTangentPhysical.representative P (μ t) (σ t)).val

/-- Actual finite physical Fourier energy of the periodic source. -/
def sourceFiniteEnergy (j : ℕ) (t : Ω) : ℝ :=
  finiteEnergy P μ (sourceRepresentative P μ σ) j t

omit [MeasurableSpace Ω] in
theorem sourceRepresentative_mem (t : Ω) :
    sourceRepresentative P μ σ t ∈ WeightedPeriodicFourierPhysical.periodicSpace P (μ t) :=
  (WeightedPeriodicTangentPhysical.representative P (μ t) (σ t)).property

omit [MeasurableSpace Ω] in
/-- The recovered norm is exactly the existing periodic variational energy. -/
theorem totalEnergy_sourceRepresentative (t : Ω) :
    totalEnergy μ (sourceRepresentative P μ σ) t =
      WeightedPeriodicTangentPhysical.energy P (μ t) (σ t) := by
  rw [WeightedPeriodicTangentPhysical.energy_eq_norm_sq]
  rfl

/-- Scalar source energy measurability is derived from finite trial energies. -/
theorem sourceEnergy_aestronglyMeasurable (ν : Measure Ω)
    (he : ∀ j,AEStronglyMeasurable (sourceFiniteEnergy P μ σ j) ν) :
    AEStronglyMeasurable (fun t => WeightedPeriodicTangentPhysical.energy P (μ t) (σ t)) ν := by
  have hh := totalEnergy_aestronglyMeasurable P μ (sourceRepresentative P μ σ) ν
    (Eventually.of_forall (sourceRepresentative_mem P μ σ)) he
  have heq : totalEnergy μ (sourceRepresentative P μ σ) =
      fun t => WeightedPeriodicTangentPhysical.energy P (μ t) (σ t) :=
    funext (totalEnergy_sourceRepresentative P μ σ)
  rwa [heq] at hh

/-- A coarse integrable bound on the actual full source energy suffices for
the periodic source's integrability. No scalar-energy measurability is assumed. -/
theorem sourceEnergy_integrable_of_full_bound (ν : Measure Ω)
    (hσ : ∀ᵐ t ∂ν,FiniteEnergy (μ t) (σ t))
    (he : ∀ j,AEStronglyMeasurable (sourceFiniteEnergy P μ σ j) ν)
    {B : Ω → ℝ} (hB : Integrable B ν)
    (hbound : ∀ᵐ t ∂ν,WeightedTangent.energy (μ t) (σ t) ≤ B t) :
    Integrable (fun t => WeightedPeriodicTangentPhysical.energy P (μ t) (σ t)) ν := by
  have hh := totalEnergy_integrable P μ (sourceRepresentative P μ σ) ν
    (Eventually.of_forall (sourceRepresentative_mem P μ σ)) he hB (by
      filter_upwards [hσ,hbound] with t ht hb
      rw [totalEnergy_sourceRepresentative]
      exact (WeightedPeriodicTangentPhysical.energy_le_full P (μ t) (σ t) ht).trans hb)
  have heq : totalEnergy μ (sourceRepresentative P μ σ) =
      fun t => WeightedPeriodicTangentPhysical.energy P (μ t) (σ t) :=
    funext (totalEnergy_sourceRepresentative P μ σ)
  rwa [heq] at hh

/-- Literal L¹ recovery of periodic variational source energies by the actual
finite Fourier trials, from a full-energy bound alone. -/
theorem source_gap_tendsto_of_full_bound (ν : Measure Ω)
    (hσ : ∀ᵐ t ∂ν,FiniteEnergy (μ t) (σ t))
    (he : ∀ j,AEStronglyMeasurable (sourceFiniteEnergy P μ σ j) ν)
    {B : Ω → ℝ} (hB : Integrable B ν)
    (hbound : ∀ᵐ t ∂ν,WeightedTangent.energy (μ t) (σ t) ≤ B t) :
    Tendsto (fun j => ∫ t,‖WeightedPeriodicTangentPhysical.energy P (μ t) (σ t)-
      sourceFiniteEnergy P μ σ j t‖ ∂ν) atTop (𝓝 0) := by
  have hh := integral_norm_gap_tendsto P μ (sourceRepresentative P μ σ) ν
    (Eventually.of_forall (sourceRepresentative_mem P μ σ)) he hB (by
      filter_upwards [hσ,hbound] with t ht hb
      rw [totalEnergy_sourceRepresentative]
      exact (WeightedPeriodicTangentPhysical.energy_le_full P (μ t) (σ t) ht).trans hb)
  simpa only [gap,totalEnergy_sourceRepresentative,sourceFiniteEnergy] using hh

end SharpWasserstein.VolterraFourier
