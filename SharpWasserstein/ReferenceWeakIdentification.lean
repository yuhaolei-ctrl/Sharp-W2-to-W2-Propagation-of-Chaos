import SharpWasserstein.WeakTimeUniqueness
import SharpWasserstein.ReferenceDriftDerivatives

/-! The actual supplied weak reference evolution is identified with the
constructed time-dependent Brownian flow. All auxiliary spatial bounds used
by uniqueness are derived from the original kernel hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ContDiff
namespace SharpWasserstein
open NoiseAverage WeightedTangent

namespace WeakEvolution
theorem eq_of_same_initial_uniform_derivatives {d N : ℕ}
    {v : ℝ → Configuration d N → Configuration d N} {P Q : ℝ → Measure (Configuration d N)}
    (hP : WeakEvolution v P) (hQ : WeakEvolution v Q)
    (hvC : Continuous (Function.uncurry v)) (hv : ∀ t, ContDiff ℝ ∞ (v t))
    (hvB : UniformAllDerivativesBounded v) (h₀ : P 0 = Q 0) {t : ℝ} (ht : 0 ≤ t) : P t = Q t := by
  letI : MeasurableSpace (Point (N*d)) := borel _
  letI : BorelSpace (Point (N*d)) := ⟨rfl⟩
  have hv' (r : ℝ) := (contDiff_infty_iff_fderiv.mp (hv r)).2
  have hv'' (r : ℝ) := (contDiff_infty_iff_fderiv.mp (hv' r)).2
  obtain ⟨K,hK⟩ := hvB.lipschitz (fun r => (hv r).differentiable (by simp))
  obtain ⟨K₁,hK₁⟩ := hvB.fderiv.lipschitz (fun r => (hv' r).differentiable (by simp))
  obtain ⟨K₂,hK₂⟩ := hvB.fderiv.fderiv.lipschitz (fun r => (hv'' r).differentiable (by simp))
  obtain ⟨M,hM₀,hM⟩ := hvB.bounded
  exact eq_of_same_initial_time_dependent hP hQ hvC hv (fun r => hvB.at r) hK hK₁ hK₂
    (M := ⟨M,hM₀⟩) hM h₀ ht
end WeakEvolution

namespace PrescribedReference
variable {d : ℕ} {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁)
  {μ : ℝ → Measure (Position d)} (hμ : IsLimitEvolution b μ)

theorem eq_law_of_weakEvolution {N : ℕ} {P : ℝ → Measure (Configuration d N)}
    (hP : WeakEvolution (fun r x i => nonlinearDrift b (μ r) (x i)) P)
    {t : ℝ} (ht : 0 ≤ t) : P t = law hb hbound hM hL₁ hμ N (P 0) t := by
  letI := hP.probability 0 le_rfl
  let v : ℝ → Configuration d N → Configuration d N :=
    fun r x i => singleDrift (b := b) (μ := μ) r (x i)
  have hPc : WeakEvolution v P := hP.congr_nonnegDrift (by
    intro r hr
    funext x i
    simp only [v,singleDrift,max_eq_right hr])
  have hQc : WeakEvolution v (law hb hbound hM hL₁ hμ N (P 0)) :=
    BrownianFlow.globalLaw_weakEvolution
      (DecoupledFlow.liftDrift_continuous N (singleDrift_continuous hb hbound hL₁ hμ))
      (DecoupledFlow.liftDrift_bound N (singleDrift_bound hbound hM hμ))
      (DecoupledFlow.liftDrift_lipschitz N (singleDrift_lipschitz hb hbound hL₁ hμ))
      (P 0) (hP.secondMoment 0 le_rfl)
  exact WeakEvolution.eq_of_same_initial_uniform_derivatives hPc hQc
    (DecoupledFlow.liftDrift_continuous N (singleDrift_continuous hb hbound hL₁ hμ))
    (DecoupledFlow.liftDrift_smooth N (singleDrift_smooth hb hμ))
    (DecoupledFlow.liftDrift_uniformAllDerivativesBounded N (singleDrift_smooth hb hμ)
      (singleDrift_uniformAllDerivativesBounded hb hμ))
    (law_initial hb hbound hM hL₁ hμ N (P 0)).symm ht

theorem singleton_eq_law {t : ℝ} (ht : 0 ≤ t) :
    singletonLaw (μ t) = law hb hbound hM hL₁ hμ 1 (singletonLaw (μ 0)) t :=
  eq_law_of_weakEvolution hb hbound hM hL₁ hμ hμ.2 ht

end PrescribedReference
end SharpWasserstein
