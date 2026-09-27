import SharpWasserstein.RegularizedTrialConvergence
import SharpWasserstein.WeightedPeriodicFourierClosure

/-! Algebraic identification of finite periodic test ranges with the span of
actual Fourier atom images under a genuine linear map. This works equally for
unit and physical-period gradient maps, without a supplied density premise. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SharpWasserstein.RegularizedTrialConvergencePeriodic
open PeriodicIntegrationByParts PeriodicFourierTests WeightedPeriodicFourier
open PeriodicSmoothGradient (SmoothPeriodicTest)
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A genuine smooth periodic atom as an element of the test vector space. -/
def atomTest (p : (Fin n → ℤ) × Bool) : SmoothPeriodicTest n :=
  ⟨atom p,smooth_atom p,periodic_atom p⟩

variable (L : SmoothPeriodicTest n →ₗ[ℝ] H)

/-- Finite Fourier potentials map into the literal algebraic atom span. -/
theorem frequency_image_mem_span {s : Finset ((Fin n → ℤ) × Bool)}
    {f : Coordinates n → ℝ} (hfs : f ∈ frequencySpace s)
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f) :
    L (⟨f,hf,hp⟩ : SmoothPeriodicTest n) ∈ Submodule.span ℝ (Set.range (fun p => L (atomTest p))) := by
  classical
  induction hfs using Submodule.span_induction with
  | mem f hmem =>
      obtain ⟨p,_,rfl⟩ := hmem
      exact Submodule.subset_span ⟨p,rfl⟩
  | zero =>
      change L 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
  | add f g hfs hgs hif hig =>
      obtain ⟨hf',hp',_⟩ := frequencySpace_properties s hfs
      obtain ⟨hg',hq',_⟩ := frequencySpace_properties s hgs
      have he : (⟨f+g,hf,hp⟩ : SmoothPeriodicTest n) =
          (⟨f,hf',hp'⟩ : SmoothPeriodicTest n)+(⟨g,hg',hq'⟩ : SmoothPeriodicTest n) := rfl
      rw [he,map_add]
      exact Submodule.add_mem _ (hif hf' hp') (hig hg' hq')
  | smul c f hfs hif =>
      obtain ⟨hf',hp',_⟩ := frequencySpace_properties s hfs
      have he : (⟨c • f,hf,hp⟩ : SmoothPeriodicTest n) =
          c • (⟨f,hf',hp'⟩ : SmoothPeriodicTest n) := rfl
      rw [he,map_smul]
      exact Submodule.smul_mem _ c (hif hf' hp')

/-- The supremum of the actual finite trial ranges is exactly the algebraic
span of the images of individual sine/cosine atoms. -/
theorem iSup_trialRange_eq_atomSpan :
    (⨆ s : Finset ((Fin n → ℤ) × Bool),(L.comp (frequencyTestInclusion s)).range) =
      Submodule.span ℝ (Set.range (fun p => L (atomTest p))) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro s y hy
    obtain ⟨f,rfl⟩ := hy
    exact frequency_image_mem_span L f.property
      (frequencySpace_properties s f.property).1 (frequencySpace_properties s f.property).2.1
  · apply Submodule.span_le.mpr
    rintro y ⟨p,rfl⟩
    apply le_iSup (fun s : Finset ((Fin n → ℤ) × Bool) => (L.comp (frequencyTestInclusion s)).range) {p}
    refine ⟨⟨atom p,?_⟩,rfl⟩
    exact Submodule.subset_span ⟨p,Finset.mem_singleton_self p,rfl⟩

/-- The closed trial space is the genuine closed atom span for any linear
realization of the smooth periodic test potentials. -/
theorem closed_trialRange_eq_atomClosure :
    (⨆ s : Finset ((Fin n → ℤ) × Bool),(L.comp (frequencyTestInclusion s)).range).topologicalClosure =
      (Submodule.span ℝ (Set.range (fun p => L (atomTest p)))).topologicalClosure := by
  rw [iSup_trialRange_eq_atomSpan L]

end SharpWasserstein.RegularizedTrialConvergencePeriodic
