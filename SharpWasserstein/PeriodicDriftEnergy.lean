import SharpWasserstein.PeriodicBochner
import SharpWasserstein.DriftEnergyIdentity

/-! The actual drift-energy cancellation on the periodic fundamental cube.
There are no boundary terms, and the surviving expression uses the genuine
Euclidean Jacobian. This supplies the smooth identity for the Galerkin limit. -/
noncomputable section
namespace SharpWasserstein.PeriodicDriftEnergy
open MeasureTheory PeriodicIntegrationByParts PeriodicFourierTests PeriodicBochner WeightedTangent
open scoped InnerProductSpace BigOperators ContDiff
variable {n : ℕ}

def vectorPullback (a : Coordinates n → Coordinates n) : Point n → Point n :=
  fun y => (coordinateEquiv n).symm (a (coordinateEquiv n y))

def drift (a : Coordinates n → Coordinates n) (f : Coordinates n → ℝ) (x : Coordinates n) : ℝ :=
  ∑ i : Fin n, a x i * coordinatePartial f i x

def divergence (a : Coordinates n → Coordinates n) (x : Coordinates n) : ℝ :=
  ∑ i : Fin n, coordinatePartial (fun y => a y i) i x

def jacobianForm (a : Coordinates n → Coordinates n) (f : Coordinates n → ℝ) (x : Coordinates n) : ℝ :=
  ⟪fderiv ℝ (vectorPullback a) ((coordinateEquiv n).symm x)
      (gradient (pullback f) ((coordinateEquiv n).symm x)),
    gradient (pullback f) ((coordinateEquiv n).symm x)⟫_ℝ

theorem inner_vector_gradient_pullback (a : Coordinates n → Coordinates n)
    (f : Coordinates n → ℝ) (y : Point n) :
    ⟪vectorPullback a y,gradient (pullback f) y⟫_ℝ = drift a f (coordinateEquiv n y) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.inner_apply,conj_trivial]
  rw [← PDEPairings.directionDeriv_eq_gradient_component,directionDeriv_pullback]
  change coordinatePartial f i (coordinateEquiv n y)*a (coordinateEquiv n y) i = _
  ring

theorem drift_energy_integrand {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f)
    {a : Coordinates n → Coordinates n} (ha : ContDiff ℝ ∞ a) (x : Coordinates n) :
    2*(∑ i : Fin n, coordinatePartial f i x*coordinatePartial (drift a f) i x)-
      drift a (gradientSquare f) x = 2*jacobianForm a f x := by
  have hA : ContDiff ℝ ∞ (vectorPullback a) :=
    (coordinateEquiv n).symm.contDiff.comp (ha.comp (coordinateEquiv n).contDiff)
  have hh := DriftEnergyIdentity.drift_energy_integrand
    (hf.comp (coordinateEquiv n).contDiff) (hA.differentiable (by simp)) ((coordinateEquiv n).symm x)
  have he : (fun y => ⟪vectorPullback a y,gradient (pullback f) y⟫_ℝ) = pullback (drift a f) :=
    funext (inner_vector_gradient_pullback a f)
  have he₂ : (fun y => ‖gradient (pullback f) y‖^2) = pullback (gradientSquare f) :=
    funext (gradientSquare_pullback f)
  change 2*⟪gradient (pullback f) ((coordinateEquiv n).symm x),
      gradient (fun y => ⟪vectorPullback a y,gradient (pullback f) y⟫_ℝ) ((coordinateEquiv n).symm x)⟫_ℝ-
    ⟪vectorPullback a ((coordinateEquiv n).symm x),
      gradient (fun y => ‖gradient (pullback f) y‖^2) ((coordinateEquiv n).symm x)⟫_ℝ = _ at hh
  rw [he,he₂,gradientPairing_pullback,inner_vector_gradient_pullback,
    ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh

theorem smooth_drift {f : Coordinates n → ℝ} (hf : ContDiff ℝ ∞ f)
    {a : Coordinates n → Coordinates n} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (drift a f) :=
  ContDiff.sum (fun i _ => ((contDiff_pi.mp ha) i).mul (smooth_coordinatePartial hf i))

theorem integral_divergence_mul {a : Coordinates n → Coordinates n}
    (ha : ContDiff ℝ 1 a) (hpa : ∀ i, Periodic (fun x => a x i))
    {g : Coordinates n → ℝ} (hg : ContDiff ℝ 1 g) (hpg : Periodic g) :
    (∫ x, divergence a x*g x ∂cube n) = -(∫ x, drift a g x ∂cube n) := by
  have hi (i : Fin n) := continuous_integrable_cube
    ((continuous_coordinatePartial ((contDiff_pi.mp ha) i) i).mul hg.continuous)
  have hj (i : Fin n) := continuous_integrable_cube
    (((contDiff_pi.mp ha) i).continuous.mul (continuous_coordinatePartial hg i))
  simp only [divergence,drift,Finset.sum_mul]
  rw [integral_finsetSum (f := fun i x => coordinatePartial (fun y => a y i) i x*g x)
      _ (fun i _ => hi i),
    integral_finsetSum (f := fun i x => a x i*coordinatePartial g i x)
      _ (fun i _ => hj i),← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hh := integral_mul_coordinatePartial hg ((contDiff_pi.mp ha) i) hpg (hpa i) (i := i)
  simpa only [mul_comm] using hh

theorem integral_drift_energy {ρ f : Coordinates n → ℝ} (hρ : ContDiff ℝ 1 ρ)
    (hpρ : Periodic ρ) (hf : ContDiff ℝ ∞ f) (hpf : Periodic f)
    {a : Coordinates n → Coordinates n} (ha : ContDiff ℝ ∞ a)
    (hpa : ∀ i, Periodic (fun x => a x i)) :
    2*(∫ x, ρ x*(∑ i : Fin n, coordinatePartial f i x*coordinatePartial (drift a f) i x) ∂cube n)+
      (∫ x, divergence (fun y => ρ y • a y) x*gradientSquare f x ∂cube n) =
      2*(∫ x, ρ x*jacobianForm a f x ∂cube n) := by
  have hA : ContDiff ℝ 1 (fun y => ρ y • a y) :=
    hρ.smul (ha.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  have hpA (i : Fin n) : Periodic (fun x => (ρ x • a x) i) := by
    intro j x
    simp only [Pi.smul_apply,smul_eq_mul,hpρ j x,hpa i j x]
  have hh := integral_divergence_mul hA hpA
    ((smooth_gradientSquare hf).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    (periodic_gradientSquare hpf)
  have he : drift (fun y => ρ y • a y) (gradientSquare f) = fun x => ρ x*drift a (gradientSquare f) x := by
    funext x
    simp only [drift,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  rw [he] at hh
  rw [hh,← sub_eq_add_neg,← integral_const_mul]
  have hi := continuous_integrable_cube (hρ.continuous.mul
    (continuous_finsetSum Finset.univ (fun i _ =>
      (smooth_coordinatePartial hf i).continuous.mul
        (smooth_coordinatePartial (smooth_drift hf ha) i).continuous)))
  have hj := continuous_integrable_cube
    (hρ.continuous.mul (smooth_drift (smooth_gradientSquare hf) ha).continuous)
  rw [← integral_sub
    (f := fun x => 2*(ρ x*(∑ i : Fin n, coordinatePartial f i x*coordinatePartial (drift a f) i x)))
    (g := fun x => ρ x*drift a (gradientSquare f) x) (hi.const_mul 2) hj,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp := congrArg (fun r => ρ x*r) (drift_energy_integrand hf ha x)
  nlinarith only [hp]

end SharpWasserstein.PeriodicDriftEnergy
