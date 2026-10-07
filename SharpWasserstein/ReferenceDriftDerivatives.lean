module

public import SharpWasserstein.Compat
public import SharpWasserstein.UniformBoundedDerivatives
public import SharpWasserstein.PrescribedReference

@[expose] public section

/-! Spatial smoothness and uniform derivative bounds for the actual averaged
reference drift, derived from the manuscript's kernel for arbitrary probability
laws, including singular laws. -/
noncomputable section
open MeasureTheory
open scoped NNReal ContDiff BigOperators
namespace SharpWasserstein
open NoiseAverage
variable {d : ℕ} {b : Position d → Position d → Position d}

theorem nonlinearDrift_smooth (hb : BoundedSmoothKernel b) (μ : ProbabilityMeasure (Position d)) :
    ContDiff ℝ ∞ (nonlinearDrift b (μ : Measure _)) := by
  let ξ : Position d → Position d × Position d := fun y => (0,y)
  let L : Position d →L[ℝ] Position d × Position d := (ContinuousLinearMap.id ℝ _).prod 0
  have hξ : StronglyMeasurable ξ := (by fun_prop : Continuous ξ).stronglyMeasurable
  have hc := (contDiff_infty_average (μ : Measure _) ξ hξ hb.smooth hb.boundedDerivatives).comp L.contDiff
  have he : (fun x => NoiseAverage.average (μ : Measure _) ξ (Function.uncurry b) (L x)) = nonlinearDrift b μ := by
    funext x
    simp only [NoiseAverage.average,nonlinearDrift,ξ,L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
      zero_apply,Prod.mk_add_mk,add_zero,zero_add,Function.uncurry_apply_pair]
  rwa [← he]

theorem nonlinearDrift_uniformAllDerivativesBounded {I : Type}
    (hb : BoundedSmoothKernel b) (μ : I → ProbabilityMeasure (Position d)) :
    UniformAllDerivativesBounded (fun t => nonlinearDrift b (μ t : Measure _)) := by
  let ξ : Position d → Position d × Position d := fun y => (0,y)
  let L : Position d →L[ℝ] Position d × Position d := (ContinuousLinearMap.id ℝ _).prod 0
  have hξ : StronglyMeasurable ξ := (by fun_prop : Continuous ξ).stronglyMeasurable
  have hc (t : I) := contDiff_infty_average (μ t : Measure _) ξ hξ hb.smooth hb.boundedDerivatives
  have hB := uniformAllDerivativesBounded_average μ ξ hξ hb.smooth hb.boundedDerivatives
  have he : (fun t x => NoiseAverage.average (μ t : Measure _) ξ (Function.uncurry b) (L x)) =
      (fun t => nonlinearDrift b (μ t : Measure _)) := by
    funext t x
    simp only [NoiseAverage.average,nonlinearDrift,ξ,L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
      zero_apply,Prod.mk_add_mk,add_zero,zero_add,Function.uncurry_apply_pair]
  rw [← he]
  exact hB.comp_linear hc L

namespace DecoupledFlow
theorem liftDrift_smooth {I : Type} (N : ℕ) {v : I → Position d → Position d}
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (t : I) :
    ContDiff ℝ ∞ (fun x : Configuration d N => fun i => v t (x i)) := by
  apply contDiff_pi.mpr
  intro i
  exact (hv t).comp (ContinuousLinearMap.proj i : Configuration d N →L[ℝ] Position d).contDiff

theorem liftDrift_uniformAllDerivativesBounded {I : Type} (N : ℕ) {v : I → Position d → Position d}
    (hv : ∀ t, ContDiff ℝ ∞ (v t)) (hB : UniformAllDerivativesBounded v) :
    UniformAllDerivativesBounded (fun t (x : Configuration d N) i => v t (x i)) := by
  let a (i : Fin N) : Position d →L[ℝ] Configuration d N :=
    ContinuousLinearMap.single ℝ (fun _ : Fin N => Position d) i
  have hc (i : Fin N) (t : I) : ContDiff ℝ ∞ (fun x : Configuration d N => v t (x i)) :=
    (hv t).comp (ContinuousLinearMap.proj i : Configuration d N →L[ℝ] Position d).contDiff
  have hBi (i : Fin N) : UniformAllDerivativesBounded (fun t (x : Configuration d N) => v t (x i)) := by
    have hh := hB.comp_linear hv (ContinuousLinearMap.proj i : Configuration d N →L[ℝ] Position d)
    exact hh
  have hBi' (i : Fin N) : UniformAllDerivativesBounded
      (fun t (x : Configuration d N) => a i (v t (x i))) := by
    have hh := (hBi i).linear_comp (hc i) (a i)
    exact hh
  have hsum : UniformAllDerivativesBounded
      (fun t (x : Configuration d N) => ∑ i : Fin N, a i (v t (x i))) :=
    UniformAllDerivativesBounded.sum
      (fun (i : Fin N) (t : I) => (a i).contDiff.comp (hc i t)) hBi'
  have he : (fun t (x : Configuration d N) => ∑ i : Fin N, a i (v t (x i))) =
      (fun t (x : Configuration d N) i => v t (x i)) := by
    funext t x
    ext i c
    simp [a,ContinuousLinearMap.single_apply,Finset.sum_apply,Pi.single_apply,ite_apply]
  exact he ▸ hsum
end DecoupledFlow

namespace PrescribedReference
variable {μ : ℝ → Measure (Position d)}

theorem singleDrift_smooth (hb : BoundedSmoothKernel b) (hμ : IsLimitEvolution b μ) (t : ℝ) :
    ContDiff ℝ ∞ (singleDrift (b := b) (μ := μ) t) :=
  nonlinearDrift_smooth hb (IsLimitEvolution.probabilityCurve hμ t)

theorem singleDrift_uniformAllDerivativesBounded
    (hb : BoundedSmoothKernel b) (hμ : IsLimitEvolution b μ) :
    UniformAllDerivativesBounded (singleDrift (b := b) (μ := μ)) :=
  nonlinearDrift_uniformAllDerivativesBounded hb (IsLimitEvolution.probabilityCurve hμ)

end PrescribedReference
end SharpWasserstein
