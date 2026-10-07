module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianSemigroup
public import SharpWasserstein.BrownianFlowWeak
public import SharpWasserstein.WeakEvolutionTimeTests

@[expose] public section

/-! Actual forward time derivatives of the constructed Brownian laws. The
initial right derivative is included. Reversing the remaining time gives a
scalar time derivative; no spatial differentiability of a backward transition
operator is asserted here. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Interval ContDiff
namespace SharpWasserstein

/-- A continuous integrated evolution on the nonnegative half-line has the
claimed derivative, including the one-sided derivative at its initial time. -/
theorem hasDerivWithinAt_nonneg_of_integral_eq
    {F G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (heq : ∀ s, 0 ≤ s → F s-F 0 = ∫ u in (0 : ℝ)..s,G u)
    {t : ℝ} (ht : 0 ≤ t) : HasDerivWithinAt F (G t) (Ici 0) t := by
  let g : ℝ → ℝ := fun u => G (max 0 u)
  have hgc : Continuous g := hG.comp_continuous (continuous_const.max continuous_id)
    (fun u => le_max_left 0 u)
  have he : ∀ s ∈ Ici (0 : ℝ), F s = F 0+∫ u in (0 : ℝ)..s,g u := by
    intro s hs
    have hi : (∫ u in (0 : ℝ)..s,g u) = ∫ u in (0 : ℝ)..s,G u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hs] at hu
      simp only [g,max_eq_right hu.1]
    rw [hi]
    linarith [heq s hs]
  have hd : HasDerivAt (fun s => F 0+∫ u in (0 : ℝ)..s,g u) (g t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 t)
      hgc.stronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt).const_add _
  have hd' := hd.hasDerivWithinAt.congr_of_mem he ht
  simpa only [g,max_eq_right ht] using hd'


namespace WeakEvolution
open WeightedTangent
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {v : ℝ → Configuration d N → Configuration d N}
  {P : ℝ → Measure (Configuration d N)}

/-- Boundary refinement of the bounded-smooth weak-evolution time derivative:
the same genuine equation gives the initial right derivative as well. -/
theorem hasDerivWithinAt_integral_bounded_smooth (h : WeakEvolution v P)
    (hv : Continuous (Function.uncurry v)) {M : ℝ}
    (hM : ∀ s x, ‖configurationEuclidean d N (v s x)‖ ≤ M)
    (f : Point (N*d) → ℝ) (hf : ContDiff ℝ ∞ f) {A B D : ℝ}
    (hfa : ∀ x, |f x| ≤ A) (hfb : ∀ x, ‖gradient f x‖ ≤ B)
    (hfd : ∀ x, |PDEPairings.laplacian f x| ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ x,f (configurationEuclidean d N x) ∂P s)
      (∫ x,generator (v t) (f ∘ configurationEuclidean d N) x ∂P t) (Ici 0) t := by
  apply hasDerivWithinAt_nonneg_of_integral_eq (t := t) ?_ ?_ ht
  · apply (continuous_generator_expectation h hv hM f hf hfb hfd).continuousOn.congr
    intro s hs
    simp only [max_eq_right (show 0 ≤ s from hs)]
  · intro s hs
    exact (equation_bounded_smooth h
      (fun u _ => (hv.comp (continuous_const.prodMk continuous_id)).measurable)
      (fun u _ => hM u) f hf hfa hfb hfd s hs).2

end WeakEvolution

namespace BrownianFlow
variable {d N : ℕ} {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ M)
  (hl : ∀ t, LipschitzWith K (v t))

/-- Continuity of the actual time-dependent generator expectation needs only
boundedness and joint continuity of the drift, and a compact smooth test. -/
theorem globalLaw_generatorExpectation_continuous
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    ContinuousOn (fun t => ∫ x,generator (v t) φ x ∂globalLaw hv hb hl μ t) (Ici 0) := by
  obtain ⟨B,_,hB⟩ := CompactGenerator.generator_uniform_bound hφ M
  exact globalLaw_boundedExpectation_continuous hv hb hl μ
    (CompactGenerator.generator_joint_continuous hφ hv)
    (fun t x => by simpa only [Real.norm_eq_abs] using hB (v t) (hb t) x)

/-- The actual forward Kolmogorov time derivative, including the initial
right derivative. It requires no initial moment assumption. -/
theorem globalLaw_hasDerivWithinAt
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ x,φ x ∂globalLaw hv hb hl μ s)
      (∫ x,generator (v t) φ x ∂globalLaw hv hb hl μ t) (Ici 0) t :=
  hasDerivWithinAt_nonneg_of_integral_eq
    (globalLaw_generatorExpectation_continuous hv hb hl μ hφ)
    (fun _ hs => globalLaw_equation hv hb hl μ hφ hs) ht

theorem globalLaw_hasDerivAt
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x,φ x ∂globalLaw hv hb hl μ s)
      (∫ x,generator (v t) φ x ∂globalLaw hv hb hl μ t) t :=
  (globalLaw_hasDerivWithinAt hv hb hl μ hφ ht.le).hasDerivAt (Ici_mem_nhds ht)

theorem globalLaw_hasDerivWithinAt_zero
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    HasDerivWithinAt (fun s => ∫ x,φ x ∂globalLaw hv hb hl μ s)
      (∫ x,generator (v 0) φ x ∂μ) (Ici 0) 0 := by
  simpa only [globalLaw_initial hv hb hl μ] using
    globalLaw_hasDerivWithinAt hv hb hl μ hφ (show (0 : ℝ) ≤ 0 from le_rfl)

/-- A point initial condition gives the genuine pointwise generator at time
zero, with precisely the manuscript's Laplacian coefficient one. -/
theorem transition_hasDerivWithinAt_zero (x : Configuration d N)
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    HasDerivWithinAt (fun s => ∫ z,φ z ∂globalLaw hv hb hl (Measure.dirac x) s)
      (generator (v 0) φ x) (Ici 0) 0 := by
  simpa only [integral_dirac] using globalLaw_hasDerivWithinAt_zero hv hb hl (Measure.dirac x) hφ

/-- Reversing the remaining duration gives a negative forward generator
expectation. This is a time derivative, without a spatial backward-PDE claim. -/
theorem globalLaw_remainingTime_hasDerivAt
    (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) {T s : ℝ} (hs : s < T) :
    HasDerivAt (fun r => ∫ x,φ x ∂globalLaw hv hb hl μ (T-r))
      (-(∫ x,generator (v (T-s)) φ x ∂globalLaw hv hb hl μ (T-s))) s := by
  have hd := (globalLaw_hasDerivAt hv hb hl μ hφ (sub_pos.mpr hs)).scomp s
    ((hasDerivAt_id s).const_sub T)
  simpa only [neg_smul,one_smul,Function.comp_def] using hd


/-- The infinitesimal transition of a propagated compact test is identified
by the actual semigroup law. Once spatial regularity of that propagated test
is established, uniqueness of the right derivative gives the backward
Kolmogorov generator identity. This theorem assumes no such regularity. -/
theorem transition_iterated_hasDerivWithinAt_zero
    {b : Configuration d N → Configuration d N}
    (hv : Continuous (Function.uncurry (fun _ : ℝ => b)))
    (hb : ∀ _ : ℝ, ∀ x, ‖b x‖ ≤ M) (hl : ∀ _ : ℝ, LipschitzWith K b)
    {T : ℝ} (hT : 0 ≤ T) (x : Configuration d N)
    {φ : Configuration d N → ℝ} (hφ : SmoothCompactTest φ) :
    HasDerivWithinAt
      (fun s => ∫ y,(∫ z,φ z ∂globalLaw hv hb hl (Measure.dirac y) T)
        ∂globalLaw hv hb hl (Measure.dirac x) s)
      (∫ z,generator b φ z ∂globalLaw hv hb hl (Measure.dirac x) T) (Ici 0) 0 := by
  have hbase : HasDerivWithinAt
      (fun s => ∫ z,φ z ∂globalLaw hv hb hl (Measure.dirac x) s)
      (∫ z,generator b φ z ∂globalLaw hv hb hl (Measure.dirac x) T) (Ici 0) (0+T) := by
    simpa only [zero_add] using globalLaw_hasDerivWithinAt hv hb hl (Measure.dirac x) hφ hT
  have hd := hbase.scomp (0 : ℝ) ((hasDerivAt_id 0).add_const T).hasDerivWithinAt
    (show MapsTo (fun s : ℝ => s+T) (Ici 0) (Ici 0) from fun s hs => add_nonneg hs hT)
  have hd' : HasDerivWithinAt
      (fun s => ∫ z,φ z ∂globalLaw hv hb hl (Measure.dirac x) (s+T))
      (∫ z,generator b φ z ∂globalLaw hv hb hl (Measure.dirac x) T) (Ici 0) 0 := by
    convert hd using 1 <;> try simp only [one_smul,Function.comp_def,id_eq]
    all_goals rfl
  obtain ⟨B,_,hB⟩ := FrozenGaussian.compact_bound hφ
  apply hd'.congr_of_mem _ (show (0 : ℝ) ∈ Ici 0 from (le_refl (0 : ℝ)))
  intro s hs
  exact (globalLaw_add_integral hv hb hl hs hT (Measure.dirac x) hφ.1.continuous hB).symm

end BrownianFlow
end SharpWasserstein
