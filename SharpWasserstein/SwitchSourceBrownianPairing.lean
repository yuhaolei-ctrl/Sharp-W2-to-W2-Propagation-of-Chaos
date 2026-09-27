import SharpWasserstein.BrownianSourceCoordinatePairing
import SharpWasserstein.SwitchSourceDerivativeFlux

/-! The actual scalar switch derivative equals the same Euclidean Brownian
propagated current whose sharp energy is estimated by the finite hierarchy. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ContDiff InnerProductSpace
namespace SharpWasserstein.SwitchSourceDerivative
open WeightedTangent PropagatedSourceEquation NoiseAverage
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Configuration d N → Configuration d N} {A H M' K' : ℝ≥0}
  (hb : ∀ x,‖b x‖ ≤ A) (hLip : LipschitzWith H b)
  (hv' : Continuous (Function.uncurry (fun _ : ℝ => equivDrift (configurationEuclidean d N) b)))
  (hb' : ∀ _ : ℝ,∀ y,‖equivDrift (configurationEuclidean d N) b y‖ ≤ M')
  (hl' : ∀ _ : ℝ,LipschitzWith K' (equivDrift (configurationEuclidean d N) b))
  {v : ℝ → Configuration d N → Configuration d N} {M K : ℝ≥0}
  (hv : Continuous (Function.uncurry v)) (hbv : ∀ r x,‖v r x‖ ≤ M)
  (hlv : ∀ r,LipschitzWith K (v r))
  {T : ℝ} (hT : 0 ≤ T) (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
  (μ : Measure (Configuration d N)) [IsProbabilityMeasure μ]

/-- Exact equality for every compact Euclidean test, with the actual
reference-minus-particle initial flux and remaining time T-s. -/
theorem sourcePairing_eq_brownianSourceAt {s : ℝ} (hs : s ∈ Icc 0 T)
    (hu : MemLp (euclideanFlux (fun x => v s x-b x)) 2
      (euclideanLaw (BrownianFlow.globalLaw hv hbv hlv μ s))) (φ : Test (N*d)) :
    letI := BrownianFlow.globalLaw_probability hv hbv hlv μ hs.1
    sourcePairing hb hLip hv hbv hlv hT μ
      ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N) s =
    Brownian.sourceAt hv' hb' hl' hT hbs hB
      (euclideanLaw (BrownianFlow.globalLaw hv hbv hlv μ s))
      (euclideanFlux (fun x => v s x-b x)) hu (T-s) φ := by
  letI := BrownianFlow.globalLaw_probability hv hbv hlv μ hs.1
  have ht : T-s ∈ Icc 0 T := ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  rw [Brownian.sourceAt_configuration_pairing (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) hv' hb' hl' hT hbs hB _ hu ht]
  unfold sourcePairing
  have he := clampedExpectation_of_mem (hLip.continuous.comp continuous_snd)
    (fun _ => hb) (fun _ => hLip) hT (BrownianNoise.configurationLaw d N T)
    ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N) ht
  change remainingTest hb hLip hT (BrownianNoise.configurationLaw d N T)
    ((φ : Point (N*d) → ℝ) ∘ configurationEuclidean d N) T s = _ at he
  rw [he]

end SharpWasserstein.SwitchSourceDerivative
