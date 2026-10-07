module

public import SharpWasserstein.Compat
public import SharpWasserstein.BrownianGaussianHistory
public import SharpWasserstein.EulerConvergence

@[expose] public section

/-! The deterministic Gaussian-history simulator is exactly the explicit Euler
recurrence driven by the supplied path increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SharpWasserstein

def gaussianHistoryCurrent {A : Type*} {d : ℕ} (initial : A → Position d) :
    (n : ℕ) → GaussianHistory A d n → Position d
  | 0, h => initial h.1
  | n+1, h => h.2 (Fin.last n)

def eulerHistoryMean {A : Type*} {d : ℕ} (initial : A → Position d)
    (b : ℝ → Position d → Position d) (δ : ℝ) (n : ℕ)
    (h : GaussianHistory A d n) : Position d :=
  gaussianHistoryCurrent initial n h + δ • b (n*δ) (gaussianHistoryCurrent initial n h)

theorem gaussianHistoryCurrent_measurable {A : Type*} [MeasurableSpace A] {d : ℕ}
    (initial : A → Position d) (hi : Measurable initial) (n : ℕ) :
    Measurable (gaussianHistoryCurrent initial n) := by
  cases n with
  | zero => exact hi.comp measurable_fst
  | succ n => exact (measurable_pi_apply (Fin.last n)).comp measurable_snd

theorem eulerHistoryMean_measurable {A : Type*} [MeasurableSpace A] {d : ℕ}
    (initial : A → Position d) (hi : Measurable initial)
    (b : ℝ → Position d → Position d) (hb : ∀ t, Measurable (b t)) (δ : ℝ) (n : ℕ) :
    Measurable (eulerHistoryMean initial b δ n) :=
  (gaussianHistoryCurrent_measurable initial hi n).add
    ((hb (n*δ)).comp (gaussianHistoryCurrent_measurable initial hi n) |>.const_smul δ)

theorem gaussianHistoryAppend_label {A : Type*} [MeasurableSpace A] {d n : ℕ}
    (a : GaussianHistory A d n → Position d) (h : GaussianHistory A d n) (z : Position d) :
    (gaussianHistoryAppend a (h,z)).1 = h.1 := rfl

theorem gaussianHistoryAppend_last {A : Type*} [MeasurableSpace A] {d n : ℕ}
    (a : GaussianHistory A d n → Position d) (h : GaussianHistory A d n) (z : Position d) :
    (gaussianHistoryAppend a (h,z)).2 (Fin.last n) = a h + z := by
  have H := congrArg Prod.snd ((gaussianHistoryStepEquiv A d n).apply_symm_apply (h,a h+z))
  exact H

theorem gaussianHistorySimulator_label {A : Type*} [MeasurableSpace A] {d : ℕ}
    (a : (n : ℕ) → GaussianHistory A d n → Position d) (n : ℕ)
    (h : GaussianHistory A d 0) (z : Configuration d n) :
    (gaussianHistorySimulator a n (h,z)).1 = h.1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih ((splitLastParticle d n z).1)

/-- Exact correspondence with `Euler.nodes`, including its `x + w 0` initial
value. The zero-path condition is explicit and is later discharged almost surely
by the actual Brownian law. -/
theorem gaussianHistorySimulator_current_eq_nodes {A : Type*} [MeasurableSpace A] {d : ℕ}
    (initial : A → Position d) (b : ℝ → Position d → Position d) (δ : ℝ)
    (w : ℝ → Position d) (hw : w 0 = 0) (h : GaussianHistory A d 0) (n : ℕ) :
    gaussianHistoryCurrent initial n (gaussianHistorySimulator (eulerHistoryMean initial b δ) n
      (h, fun i : Fin n => w ((i+1)*δ) - w (i*δ))) = Euler.nodes b (initial h.1) w δ n := by
  induction n with
  | zero => simp [gaussianHistoryCurrent, gaussianHistorySimulator, Euler.nodes, hw]
  | succ n ih =>
    change (gaussianHistoryAppend _ (_, _)).2 (Fin.last n) = _
    rw [gaussianHistoryAppend_last]
    have hp : (splitLastParticle d n (fun i : Fin (n+1) => w ((i+1)*δ)-w (i*δ))).1 =
        (fun i : Fin n => w ((i+1)*δ)-w (i*δ)) := by
      funext i
      rw [splitLastParticle_apply]
      rfl
    rw [hp]
    change eulerHistoryMean initial b δ n _ + (w ((n+1)*δ)-w (n*δ)) = _
    rw [eulerHistoryMean, ih, Euler.nodes]

/-- Label-dependent drifts cover the controlled bridge built from an initial coupling. -/
def eulerLabelHistoryMean {A : Type*} {d : ℕ} (initial : A → Position d)
    (b : A → ℝ → Position d → Position d) (δ : ℝ) (n : ℕ)
    (h : GaussianHistory A d n) : Position d :=
  gaussianHistoryCurrent initial n h + δ • b h.1 (n*δ) (gaussianHistoryCurrent initial n h)

theorem eulerLabelHistoryMean_measurable {A : Type*} [MeasurableSpace A] {d : ℕ}
    (initial : A → Position d) (hi : Measurable initial)
    (b : A → ℝ → Position d → Position d)
    (hb : ∀ t, Measurable (fun p : A × Position d => b p.1 t p.2)) (δ : ℝ) (n : ℕ) :
    Measurable (eulerLabelHistoryMean initial b δ n) :=
  (gaussianHistoryCurrent_measurable initial hi n).add
    ((hb (n*δ)).comp (measurable_fst.prodMk (gaussianHistoryCurrent_measurable initial hi n)) |>.const_smul δ)

theorem gaussianHistorySimulator_label_current_eq_nodes {A : Type*} [MeasurableSpace A] {d : ℕ}
    (initial : A → Position d) (b : A → ℝ → Position d → Position d) (δ : ℝ)
    (w : ℝ → Position d) (hw : w 0 = 0) (h : GaussianHistory A d 0) (n : ℕ) :
    gaussianHistoryCurrent initial n (gaussianHistorySimulator (eulerLabelHistoryMean initial b δ) n
      (h, fun i : Fin n => w ((i+1)*δ) - w (i*δ))) = Euler.nodes (b h.1) (initial h.1) w δ n := by
  induction n with
  | zero => simp [gaussianHistoryCurrent, gaussianHistorySimulator, Euler.nodes, hw]
  | succ n ih =>
    change (gaussianHistoryAppend _ (_, _)).2 (Fin.last n) = _
    rw [gaussianHistoryAppend_last]
    have hp : (splitLastParticle d n (fun i : Fin (n+1) => w ((i+1)*δ)-w (i*δ))).1 =
        (fun i : Fin n => w ((i+1)*δ)-w (i*δ)) := by
      funext i
      rw [splitLastParticle_apply]
      rfl
    rw [hp]
    change eulerLabelHistoryMean initial b δ n _ + (w ((n+1)*δ)-w (n*δ)) = _
    rw [eulerLabelHistoryMean, ih, gaussianHistorySimulator_label, Euler.nodes]

end SharpWasserstein
