module

public import SharpWasserstein.Compat
public import SharpWasserstein.PeriodicConvolutionTestGradient
public import SharpWasserstein.PeriodicConvolutionApproximation
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! Uniform approximation by the actual positive periodic convolution kernels.
The norm limit is proved in the Banach space of continuous functions on the
compact torus, so it applies uniformly, including under singular measures. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace SharpWasserstein.WeightedPeriodicFourier
open PeriodicIntegrationByParts PeriodicTorusBridge PeriodicPositiveKernel PeriodicConvolution
variable {n : ℕ}

theorem continuous_integrable_cube_banach {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SecondCountableTopology E] {g : Coordinates n → E}
    (hg : Continuous g) : Integrable g (cube n) := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := (hc.image hg).isBounded.exists_norm_le
  exact Integrable.of_bound hg.aestronglyMeasurable C ((cube_ae_mem n).mono
    (fun x hx => hC _ ⟨x, hx, rfl⟩))

def translatedLift (f : Coordinates n → ℝ) (hp : Periodic f) (hf : Continuous f) :
    C(Coordinates n, C(UnitAddTorus (Fin n), ℝ)) :=
  (⟨fun p : Coordinates n × UnitAddTorus (Fin n) =>
    continuousLift f hp hf (p.2 + toTorus p.1),
    (continuousLift f hp hf).continuous.comp
      (continuous_snd.add ((toTorus_continuous n).comp continuous_fst))⟩ :
    C(Coordinates n × UnitAddTorus (Fin n), ℝ)).curry

theorem translatedLift_periodic (f : Coordinates n → ℝ) (hp : Periodic f)
    (hf : Continuous f) (i : Fin n) :
    Function.Periodic (translatedLift f hp hf) (Pi.single i 1) := by
  intro x
  ext y
  change continuousLift f hp hf (y + toTorus (x + Pi.single i 1)) =
    continuousLift f hp hf (y + toTorus x)
  congr 2
  ext j
  by_cases h : j = i
  · subst j
    simp [toTorus]
  · simp [toTorus, Pi.single_eq_of_ne h]

theorem translatedLift_zero (f : Coordinates n → ℝ) (hp : Periodic f)
    (hf : Continuous f) : translatedLift f hp hf 0 = continuousLift f hp hf := by
  ext y
  change continuousLift f hp hf (y + toTorus 0) = continuousLift f hp hf y
  have h : toTorus (0 : Coordinates n) = 0 := by ext i; simp [toTorus]
  rw [h, add_zero]

theorem translatedLift_integral_apply (κ : ℝ) (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : Continuous f) (y : Coordinates n) :
    (∫ z, kernel κ z • translatedLift f hp hf z ∂cube n) (toTorus y) =
      testAverage κ f y := by
  have hi : Integrable (fun z => kernel κ z • translatedLift f hp hf z) (cube n) :=
    continuous_integrable_cube_banach (Continuous.smul (f := kernel κ)
      (g := fun z => translatedLift f hp hf z) (kernel_smooth n κ).continuous
      (translatedLift f hp hf).continuous)
  rw [ContinuousMap.integral_apply hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change kernel κ z * continuousLift f hp hf (toTorus y + toTorus z) = _
    have he : toTorus y + toTorus z = toTorus (y+z) := by
      ext i
      simp [toTorus]
    rw [he]
    exact congrArg (kernel κ z * ·) (lift_toTorus hp (y+z))

theorem testAverage_uniform_tendsto (f : Coordinates n → ℝ)
    (hp : Periodic f) (hf : Continuous f) :
    ∀ ε > 0, ∀ᶠ k : ℕ in atTop, ∀ y,
      |testAverage (k : ℝ) f y - f y| < ε := by
  intro ε hε
  have ht := integral_kernel_tendsto (translatedLift_periodic f hp hf)
    (translatedLift f hp hf).continuous
  rw [translatedLift_zero] at ht
  have htn : Tendsto (fun k : ℕ => ‖(∫ z, kernel (k : ℝ) z • translatedLift f hp hf z ∂cube n) -
      continuousLift f hp hf‖) atTop (𝓝 0) := by
    simpa using (ht.sub (tendsto_const_nhds (x := continuousLift f hp hf))).norm
  have he := (tendsto_order.1 htn).2 ε hε
  filter_upwards [he] with k hk
  intro y
  have hbound := ContinuousMap.norm_coe_le_norm
    ((∫ z, kernel (k : ℝ) z • translatedLift f hp hf z ∂cube n) -
      continuousLift f hp hf) (toTorus y)
  change |(∫ z, kernel (k : ℝ) z • translatedLift f hp hf z ∂cube n) (toTorus y) -
    continuousLift f hp hf (toTorus y)| ≤ _ at hbound
  rw [translatedLift_integral_apply] at hbound
  change |testAverage (k : ℝ) f y - lift f (toTorus y)| ≤ _ at hbound
  rw [lift_toTorus hp] at hbound
  exact hbound.trans_lt hk

end SharpWasserstein.WeightedPeriodicFourier
