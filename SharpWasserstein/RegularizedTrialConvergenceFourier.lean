import SharpWasserstein.RegularizedTrialConvergence
import SharpWasserstein.FiniteGradientTrial
import SharpWasserstein.WeightedPeriodicFourierClosure

/-! Concrete recovery for actual finite Fourier gradient operators in a
possibly singular finite carrying measure. The closure is the proved weighted
periodic gradient closure, and the coefficient operator is exactly the one
used by `FiniteGradientTrial`, not a postulated dense trial family. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace
namespace SharpWasserstein.RegularizedTrialConvergenceFourier
open WeightedTangent PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner
open PeriodicSmoothGradient (SmoothPeriodicTest)
open WeightedPeriodicFourier RegularizedTrialConvergence

abbrev Atom (n : ℕ) := (Fin n → ℤ) × Bool
variable {n : ℕ}

/-- The literal bounded smooth Euclidean Fourier potential. -/
def atomPotential (p : Atom n) : Point n → ℝ := pullback (atom p)

theorem atomPotential_smooth (p : Atom n) : ContDiff ℝ ∞ (atomPotential p) :=
  (smooth_atom p).comp (coordinateEquiv n).contDiff

theorem atomPotential_gradient_bound (p : Atom n) :
    ∃ B : ℝ,∀ x,‖gradient (atomPotential p) x‖ ≤ B :=
  pullback_gradient_bound (atom p) (smooth_atom p) (periodic_atom p)

variable [MeasurableSpace (Point n)] [BorelSpace (Point n)]
  (μ : Measure (Point n)) [IsFiniteMeasure μ]

/-- A Fourier atom's genuine weighted gradient. -/
def atomVector (p : Atom n) : Lp (Point n) 2 μ :=
  (WeightedPeriodicFourier.gradientVector μ (atom p) (smooth_atom p) (periodic_atom p)).val

/-- Every finite Fourier gradient is in the actual algebraic span of the
weighted atom gradients, before any closure or limiting argument. -/
theorem frequency_gradient_mem_atomSpan {s : Finset (Atom n)}
    {f : Coordinates n → ℝ} (hfs : f ∈ frequencySpace s)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    (WeightedPeriodicFourier.gradientVector μ f hf hp).val ∈
      Submodule.span ℝ (Set.range (atomVector μ)) := by
  classical
  induction hfs using Submodule.span_induction with
  | mem f hmem =>
      obtain ⟨p,_,rfl⟩ := hmem
      exact Submodule.subset_span ⟨p,rfl⟩
  | zero =>
      change ((periodicGradientMap μ) (0 : SmoothPeriodicTest n)).val ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
  | add f g hfs hgs hif hig =>
      obtain ⟨hf',hp',_⟩ := frequencySpace_properties s hfs
      obtain ⟨hg',hq',_⟩ := frequencySpace_properties s hgs
      have hif' := hif hf' hp'
      have hig' := hig hg' hq'
      change ((periodicGradientMap μ) (⟨f+g,hf,hp⟩ : SmoothPeriodicTest n)).val ∈ _
      have he : (⟨f+g,hf,hp⟩ : SmoothPeriodicTest n) =
          (⟨f,hf',hp'⟩ : SmoothPeriodicTest n)+(⟨g,hg',hq'⟩ : SmoothPeriodicTest n) := rfl
      rw [he,map_add,Submodule.coe_add]
      exact Submodule.add_mem _ hif' hig'
  | smul c f hfs hif =>
      obtain ⟨hf',hp',_⟩ := frequencySpace_properties s hfs
      have hif' := hif hf' hp'
      change ((periodicGradientMap μ) (⟨c • f,hf,hp⟩ : SmoothPeriodicTest n)).val ∈ _
      have he : (⟨c • f,hf,hp⟩ : SmoothPeriodicTest n) =
          c • (⟨f,hf',hp'⟩ : SmoothPeriodicTest n) := rfl
      rw [he,map_smul,Submodule.coe_smul]
      exact Submodule.smul_mem _ c hif'

/-- Membership in the independently proved weighted periodic closure implies
membership in the genuine closed atom span in the ambient weighted `L²`. -/
theorem periodic_mem_atomClosure {U : gradientClosure μ}
    (hU : U ∈ WeightedPeriodicFourier.periodicSpace μ) :
    U.val ∈ (Submodule.span ℝ (Set.range (atomVector μ))).topologicalClosure := by
  let S := (Submodule.span ℝ (Set.range (atomVector μ))).topologicalClosure
  have hle : WeightedPeriodicFourier.periodicSpace μ ≤
      S.comap (gradientClosure μ).subtype := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro s V hV
      obtain ⟨f,rfl⟩ := hV
      change (WeightedPeriodicFourier.gradientVector μ f.val
        (frequencySpace_properties s f.property).1
        (frequencySpace_properties s f.property).2.1).val ∈ S
      exact (Submodule.span ℝ (Set.range (atomVector μ))).le_topologicalClosure
        (frequency_gradient_mem_atomSpan μ f.property _ _)
    · exact (Submodule.span ℝ (Set.range (atomVector μ))).isClosed_topologicalClosure.preimage
        (gradientClosure μ).subtypeL.continuous
  exact hle hU

/-- The finite trial operator is precisely the actual weighted gradient map
of the Fourier potentials in `FiniteGradientTrial`. -/
def trial (s : Finset (Atom n)) : EuclideanSpace ℝ s →L[ℝ] Lp (Point n) 2 μ :=
  FiniteGradientTrial.gradientMap μ (fun p : s => atomPotential p.val)
    (fun p => atomPotential_smooth p.val) (fun p => atomPotential_gradient_bound p.val)

theorem trial_eq_synthesis (s : Finset (Atom n)) : trial μ s = synthesis (atomVector μ) s := by
  apply ContinuousLinearMap.ext
  intro c
  rw [trial,FiniteGradientTrial.gradientMap_apply,synthesis_apply]
  apply Finset.sum_congr rfl
  intro p _
  rfl

/-- Concrete convergence of the genuine coefficient-regularized Fourier
trial energy, including singular finite carrying measures. -/
theorem energy_tendsto {J : Type*} {l : Filter J}
    (s : J → Finset (Atom n)) (δ : J → ℝ)
    (hs : ∀ p,∀ᶠ j in l,p ∈ s j) (hδpos : ∀ j,0 < δ j)
    (hδ : Tendsto δ l (𝓝 0)) (U : gradientClosure μ)
    (hU : U ∈ WeightedPeriodicFourier.periodicSpace μ) :
    Tendsto (fun j => RegularizedTrialEnergy.energy (trial μ (s j)) (δ j) U.val)
      l (𝓝 (‖U‖^2)) := by
  simpa only [trial_eq_synthesis,Submodule.norm_coe] using
    RegularizedTrialConvergence.energy_tendsto (atomVector μ) s δ hs hδpos hδ U.val
      (periodic_mem_atomClosure μ hU)

end SharpWasserstein.RegularizedTrialConvergenceFourier
