import SharpWasserstein.WeakAutonomousUniqueness
import SharpWasserstein.BoundedDerivativeLinear
import SharpWasserstein.BrownianParticleWeak

/-! The manuscript's actual arbitrary weak particle evolution is identified
with the constructed Brownian particle law. All spatial regularity required
for uniqueness is derived from the stated interaction-kernel hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ContDiff BigOperators
namespace SharpWasserstein
open NoiseAverage WeightedTangent

theorem particleDrift_allDerivativesBounded {d N : ℕ}
    {b : Position d → Position d → Position d} (hb : BoundedSmoothKernel b) :
    AllDerivativesBounded (particleDrift (N := N) b) := by
  let e (i j : Fin N) : Configuration d N →L[ℝ] Position d × Position d :=
    (ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j)
  let a (i : Fin N) : Position d →L[ℝ] Configuration d N :=
    ContinuousLinearMap.single ℝ (fun _ : Fin N => Position d) i
  have hc (i j : Fin N) : ContDiff ℝ ∞ (fun x : Configuration d N => b (x i) (x j)) := hb.smooth.comp (e i j).contDiff
  have hB (i j : Fin N) : AllDerivativesBounded (fun x : Configuration d N => b (x i) (x j)) :=
    AllDerivativesBounded.comp_linear hb.smooth hb.boundedDerivatives (e i j)
  have hc' (i j : Fin N) : ContDiff ℝ ∞ (fun x : Configuration d N => a i (b (x i) (x j))) := (a i).contDiff.comp (hc i j)
  have hB' (i j : Fin N) : AllDerivativesBounded (fun x : Configuration d N => a i (b (x i) (x j))) :=
    (hB i j).linear_comp (hc i j) (a i)
  have hs : ContDiff ℝ ∞ (fun x : Configuration d N => ∑ i : Fin N, ∑ j : Fin N, a i (b (x i) (x j))) :=
    ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => hc' i j))
  have hsum : AllDerivativesBounded (fun x : Configuration d N => ∑ i : Fin N, ∑ j : Fin N, a i (b (x i) (x j))) :=
    AllDerivativesBounded.sum Finset.univ
      (fun i _ => ContDiff.sum (fun j _ => hc' i j))
      (fun i _ => AllDerivativesBounded.sum Finset.univ (fun j _ => hc' i j) (fun j _ => hB' i j))
  have he : (fun x : Configuration d N => (N:ℝ)⁻¹ • ∑ i : Fin N, ∑ j : Fin N, a i (b (x i) (x j))) =
      particleDrift (N := N) b := by
    funext x
    ext i c
    simp [a,particleDrift,ContinuousLinearMap.single_apply,Finset.sum_apply,Pi.single_apply]
  rw [← he]
  exact hsum.const_smul hs (N:ℝ)⁻¹

namespace BrownianParticle
variable {d N : ℕ} [MeasurableSpace (Point (N*d))] [BorelSpace (Point (N*d))]
  {b : Position d → Position d → Position d} {M L₁ L₂ : ℝ}
  (hN : 0 < N) (hb : BoundedSmoothKernel b) (hbound : KernelBounds b M L₁ L₂)
  (hM : 0 ≤ M) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)

theorem eq_globalLaw_of_weakEvolution {P : ℝ → Measure (Configuration d N)}
    (hP : WeakEvolution (fun _ => particleDrift b) P) {t : ℝ} (ht : 0 ≤ t) :
    P t = globalLaw hN hb hbound hM hL₁ hL₂ (P 0) t := by
  letI := hP.probability 0 le_rfl
  apply WeakEvolution.eq_of_same_initial_autonomous hP
    (globalLaw_weakEvolution hN hb hbound hM hL₁ hL₂ (P 0) (hP.secondMoment 0 le_rfl))
    (particleDrift_smooth hb) (particleDrift_allDerivativesBounded hb) _ ht
  exact (globalLaw_initial hN hb hbound hM hL₁ hL₂ (P 0)).symm

end BrownianParticle
end SharpWasserstein
