import SharpWasserstein.EulerBrownianLaw
import SharpWasserstein.GaussianBridgeCoupling

/-! Gaussian meeting-bridge endpoint observations are the actual Brownian Euler
endpoint laws, in the exact direction used for entropy-cost comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SharpWasserstein

theorem configurationFlatten_symm_add {d N : ℕ} (x y : Position (N*d)) :
    (configurationFlatten d N).symm (x+y) =
      (configurationFlatten d N).symm x + (configurationFlatten d N).symm y := by
  apply (configurationFlatten d N).injective
  simp

theorem configurationFlatten_symm_sub {d N : ℕ} (x y : Position (N*d)) :
    (configurationFlatten d N).symm (x-y) =
      (configurationFlatten d N).symm x - (configurationFlatten d N).symm y := by
  apply (configurationFlatten d N).injective
  simp

theorem configurationFlatten_symm_smul {d N : ℕ} (c : ℝ) (x : Position (N*d)) :
    (configurationFlatten d N).symm (c • x) = c • (configurationFlatten d N).symm x := by
  apply (configurationFlatten d N).injective
  simp

theorem flattenedDrift_shifted {d N : ℕ}
    (b : ℝ → Configuration d N → Configuration d N) (x y : Position (N*d)) (T : ℝ) :
    flattenedDrift (EulerBridge.shiftedDrift b ((configurationFlatten d N).symm x)
      ((configurationFlatten d N).symm y) T) =
      EulerBridge.shiftedDrift (flattenedDrift b) x y T := by
  funext t z
  simp only [flattenedDrift, EulerBridge.shiftedDrift, configurationFlatten_add,
    configurationFlatten_smul, configurationFlatten_sub, MeasurableEquiv.apply_symm_apply,
    configurationFlatten_symm_add, configurationFlatten_symm_smul, configurationFlatten_symm_sub]

namespace GaussianBridge

def initialX {d N : ℕ} (z : Labels (N*d)) : Configuration d N := (configurationFlatten d N).symm z.1
def initialY {d N : ℕ} (z : Labels (N*d)) : Configuration d N := (configurationFlatten d N).symm z.2

theorem measurable_initialX (d N : ℕ) : Measurable (initialX (d := d) (N := N)) :=
  (configurationFlatten d N).symm.measurable.comp measurable_fst

theorem measurable_initialY (d N : ℕ) : Measurable (initialY (d := d) (N := N)) :=
  (configurationFlatten d N).symm.measurable.comp measurable_snd

def endpointObservation {d N : ℕ} (j : ℕ) (h : History (N*d) j) : Configuration d N :=
  (configurationFlatten d N).symm (state j h)

theorem endpointObservation_measurable {d N : ℕ} (j : ℕ) :
    Measurable (endpointObservation (d := d) (N := N) j) :=
  (configurationFlatten d N).symm.measurable.comp (measurable_state j)

theorem current_initialX {d N : ℕ} (j : ℕ) (h : History (N*d) j) :
    gaussianHistoryCurrent (fun z => configurationFlatten d N (initialX z)) j h = state j h := by
  cases j with
  | zero => exact (configurationFlatten d N).apply_symm_apply h.1.1
  | succ j => rfl

theorem mean_ordinary_eq {d N : ℕ} (b : ℝ → Configuration d N → Configuration d N) (δ : ℝ≥0) :
    configurationEulerMean (initialX (d := d) (N := N)) (fun _ => b) δ =
      ordinaryMean (flattenedDrift b) δ := by
  funext j h
  simp only [configurationEulerMean, eulerLabelHistoryMean, current_initialX, ordinaryMean]

theorem mean_shifted_eq {d N : ℕ} (b : ℝ → Configuration d N → Configuration d N) (T : ℝ) (δ : ℝ≥0) :
    configurationEulerMean (initialX (d := d) (N := N))
      (fun z => EulerBridge.shiftedDrift b (initialX z) (initialY z) T) δ =
      shiftedMean (flattenedDrift b) T δ := by
  funext j h
  simp only [configurationEulerMean, eulerLabelHistoryMean, current_initialX, shiftedMean]
  simp only [initialX, initialY, flattenedDrift_shifted]

theorem observation_eq {d N : ℕ} (j : ℕ) :
    configurationEulerObservation (initialX (d := d) (N := N)) j = endpointObservation j := by
  funext h
  simp only [configurationEulerObservation, current_initialX, endpointObservation]

def brownianEndpointX {d N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (b : ℝ → Configuration d N → Configuration d N) (n : ℕ)
    (p : Labels (N*d) × C(Icc 0 T, Configuration d N)) : Configuration d N :=
  Euler.nodes b (initialX p.1) (BoundedFlow.noiseExtension hT p.2) (T/(n+1)) (n+1)

def brownianEndpointY {d N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (b : ℝ → Configuration d N → Configuration d N) (n : ℕ)
    (p : Labels (N*d) × C(Icc 0 T, Configuration d N)) : Configuration d N :=
  Euler.nodes b (initialY p.1) (BoundedFlow.noiseExtension hT p.2) (T/(n+1)) (n+1)

theorem ordinaryLaw_endpoint_eq {d N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (γ : Measure (Labels (N*d))) [IsProbabilityMeasure γ]
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (n : ℕ) :
    (ordinaryLaw γ (flattenedDrift b) (flattenedDrift_measurable b hb)
      (NNReal.mk (T/(n+1)) (by positivity)) (n+1)).map (endpointObservation (d := d) (N := N) (n+1)) =
      (γ.prod (BrownianNoise.configurationLaw d N T)).map (brownianEndpointX hT b n) := by
  have h := configurationEuler_brownian_hasLaw hT γ initialX (measurable_initialX d N)
    (fun _ => b) (fun t => (hb t).comp measurable_snd) n
  have hm := mean_ordinary_eq b ((NNReal.mk (T/(n+1)) (by positivity)) : ℝ≥0)
  change configurationEulerMean initialX (fun _ => b) (T/(n+1)) = _ at hm
  simp only [hm, observation_eq] at h
  exact h.map_eq.symm

theorem shiftedLaw_endpoint_eq {d N : ℕ} {T : ℝ} (hT : 0 < T)
    (γ : Measure (Labels (N*d))) [IsProbabilityMeasure γ]
    (b : ℝ → Configuration d N → Configuration d N) (hb : ∀ t, Measurable (b t)) (n : ℕ) :
    (shiftedLaw γ (flattenedDrift b) (flattenedDrift_measurable b hb) T
      (NNReal.mk (T/(n+1)) (by positivity)) (n+1)).map (endpointObservation (d := d) (N := N) (n+1)) =
      (γ.prod (BrownianNoise.configurationLaw d N T)).map (brownianEndpointY hT.le b n) := by
  have hmshift : ∀ t, Measurable (fun p : Labels (N*d) × Configuration d N =>
      EulerBridge.shiftedDrift b (initialX p.1) (initialY p.1) T t p.2) := by
    intro t
    have hx : Measurable (fun p : Labels (N*d) × Configuration d N => initialX p.1) :=
      (measurable_initialX d N).comp measurable_fst
    have hy : Measurable (fun p : Labels (N*d) × Configuration d N => initialY p.1) :=
      (measurable_initialY d N).comp measurable_fst
    exact ((hb t).comp (measurable_snd.add ((hy.sub hx).const_smul (1-t/T)))).add
      ((hy.sub hx).const_smul T⁻¹)
  have h := configurationEuler_brownian_hasLaw hT.le γ initialX (measurable_initialX d N)
    (fun z => EulerBridge.shiftedDrift b (initialX z) (initialY z) T) hmshift n
  have hm := mean_shifted_eq b T ((NNReal.mk (T/(n+1)) (by positivity)) : ℝ≥0)
  change configurationEulerMean initialX (fun z => EulerBridge.shiftedDrift b (initialX z) (initialY z) T) (T/(n+1)) = _ at hm
  simp only [hm, observation_eq] at h
  have he : (fun p : Labels (N*d) × C(Icc 0 T, Configuration d N) =>
      Euler.nodes (EulerBridge.shiftedDrift b (initialX p.1) (initialY p.1) T)
        (initialX p.1) (BoundedFlow.noiseExtension hT.le p.2) (T/(n+1)) (n+1)) =
      brownianEndpointY hT.le b n := by
    funext p
    exact EulerBridge.endpoint_conjugacy b (initialX p.1) (initialY p.1) _ hT n
  rw [he] at h
  exact h.map_eq.symm

end GaussianBridge
end SharpWasserstein
