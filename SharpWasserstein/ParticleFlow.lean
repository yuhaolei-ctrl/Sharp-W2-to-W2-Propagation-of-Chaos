import SharpWasserstein.FlowMoments
import SharpWasserstein.EuclideanFlow
import SharpWasserstein.RandomMapTransport

/-! Constructed particle solution maps, probability laws, moment propagation,
and genuine Wasserstein stability. Brownian distributional properties and
identification with the weak Fokker--Planck equation are separate obligations. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace SharpWasserstein

variable {d N : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}

/-- Bounded interaction gives a configuration sup-norm bound without an N factor. -/
theorem particleDrift_norm_bound (hN : 0 < N) (hbound : KernelBounds b M L₁ L₂)
    (hM : 0 ≤ M) (x : Configuration d N) : ‖particleDrift b x‖ ≤ M :=
  (pi_norm_le_iff_of_nonneg hM).mpr (particleDrift_coordinate_bound hN hbound x)

namespace ParticleFlow

variable (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)

/-- Solve the actual particle integral equation for each initial configuration
and each continuous additive path. -/
def solution {T : ℝ} (hT : 0 ≤ T) (x : Configuration d N)
    (w : C(Icc 0 T, Configuration d N)) : ℝ → Configuration d N :=
  BoundedFlow.flow (v := fun _ => particleDrift b)
    ((particleDrift_lipschitz hN hb hbound hL₁ hL₂).continuous.comp continuous_snd)
    (M := ⟨M, hM⟩) (fun _ x => particleDrift_norm_bound hN hbound hM x)
    (fun _ => particleDrift_lipschitz hN hb hbound hL₁ hL₂) hT x w

theorem solution_trajectory {T : ℝ} (hT : 0 ≤ T) (x : Configuration d N)
    (w : C(Icc 0 T, Configuration d N)) :
    FiniteAdditiveTrajectory (fun _ => particleDrift b) (BoundedFlow.noiseExtension hT w)
      x T (solution hN hb hbound hM hL₁ hL₂ hT x w) :=
  BoundedFlow.flow_trajectory _ _ _ hT x w

theorem solution_continuous {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      solution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 t) :=
  BoundedFlow.flow_continuous _ _ _ hT ht

theorem solution_measurable {T : ℝ}
    [MeasurableSpace C(Icc 0 T, Configuration d N)] [BorelSpace C(Icc 0 T, Configuration d N)]
    (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Measurable (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      solution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 t) :=
  (solution_continuous hN hb hbound hM hL₁ hL₂ hT ht).measurable

/-- Uniqueness is proved for every competing continuous integral solution. -/
theorem solution_unique {T : ℝ} (hT : 0 ≤ T) (x : Configuration d N)
    (w : C(Icc 0 T, Configuration d N)) {X : ℝ → Configuration d N}
    (hX : FiniteAdditiveTrajectory (fun _ => particleDrift b)
      (BoundedFlow.noiseExtension hT w) x T X) {t : ℝ} (ht : t ∈ Icc 0 T) :
    solution hN hb hbound hM hL₁ hL₂ hT x w t = X t :=
  BoundedFlow.flow_eq_of_trajectory _ _ _ hT x w hX ht

variable {T : ℝ} [MeasurableSpace C(Icc 0 T, Configuration d N)]
  [BorelSpace C(Icc 0 T, Configuration d N)]

/-- Actual solution law from independent initial data and continuous noise. -/
def law (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Configuration d N)) (t : ℝ) : Measure (Configuration d N) :=
  randomMapLaw (fun p => solution hN hb hbound hM hL₁ hL₂ hT p.1 p.2 t) μ ξ

theorem law_probability (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ] {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (law hN hb hbound hM hL₁ hL₂ hT μ ξ t) :=
  randomMapLaw_probability _ (solution_measurable hN hb hbound hM hL₁ hL₂ hT ht) μ ξ

/-- The law has finite second moment whenever the initial configuration and
the current noise value do. No noise-supremum moment is assumed. -/
theorem law_secondMoment (hT : 0 ≤ T) (μ : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ] (hμ : HasSecondMoment μ)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hξ : MemLp (fun w : C(Icc 0 T, Configuration d N) => w ⟨t, ht⟩) 2 ξ) :
    HasSecondMoment (law hN hb hbound hM hL₁ hL₂ hT μ ξ t) := by
  have hx : MemLp (fun p : Configuration d N × C(Icc 0 T, Configuration d N) => p.1)
      2 (μ.prod ξ) := by
    apply memLp_of_hasSecondMoment_map measurable_fst
    rwa [(measurePreserving_fst (μ := μ) (ν := ξ)).map_eq]
  have hw : MemLp (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      BoundedFlow.noiseExtension hT p.2 t) 2 (μ.prod ξ) := by
    simpa only [Function.comp_def, BoundedFlow.noiseExtension, projIcc_of_mem _ ht] using
      hξ.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := ξ))
  apply hasSecondMoment_map_of_memLp (solution_measurable hN hb hbound hM hL₁ hL₂ hT ht)
  exact finiteTrajectory_memLp
    (fun p : Configuration d N × C(Icc 0 T, Configuration d N) =>
      solution_trajectory hN hb hbound hM hL₁ hL₂ hT p.1 p.2)
    (fun _ _ x => particleDrift_norm_bound hN hbound hM x) ht hx hw
    (solution_measurable hN hb hbound hM hL₁ hL₂ hT ht).aestronglyMeasurable

/-- Stability of the constructed particle laws for the true unnormalized
quadratic transport cost, with exponent independent of particle number. -/
theorem law_wassersteinSq_le (hT : 0 ≤ T) (μ ν : Measure (Configuration d N))
    (ξ : Measure C(Icc 0 T, Configuration d N))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    wassersteinSq (law hN hb hbound hM hL₁ hL₂ hT μ ξ t)
      (law hN hb hbound hM hL₁ hL₂ hT ν ξ t) ≤
      ENNReal.ofReal (Real.exp (Real.sqrt (2 * d * (L₁ ^ 2 + L₂ ^ 2)) * t) ^ 2) *
        wassersteinSq μ ν := by
  apply wassersteinSq_randomMapLaw_le _
    (solution_measurable hN hb hbound hM hL₁ hL₂ hT ht) ξ μ ν (by positivity)
  intro x y w
  exact particleTrajectory_productCost_le hN hb hbound hL₁ hL₂
    (solution_trajectory hN hb hbound hM hL₁ hL₂ hT x w)
    (solution_trajectory hN hb hbound hM hL₁ hL₂ hT y w) ht

end ParticleFlow
end SharpWasserstein
