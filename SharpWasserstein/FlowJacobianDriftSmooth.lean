module

public import SharpWasserstein.Compat
public import SharpWasserstein.FlowJacobianDriftConvergence
public import SharpWasserstein.DriftApproximation

@[expose] public section

/-! Direct bounded-smooth drift APIs. Individual bounds on second derivatives
are derived from the actual hypotheses, and locally uniform drift convergence
supplies convergence of the actual selected flows. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology Interval ContDiff
namespace SharpWasserstein.FlowJacobianDrift
open FlowInitialDerivative NoiseAverage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- The smooth bounded-derivative assumptions supply all individual
variational constructions; no uniform second-derivative bound is needed. -/
theorem jacobian_tendstoUniformlyOn_of_boundedSmooth
    {bk : ℕ → E → E} {b : E → E} {M K : ℝ≥0}
    (hbk : ∀ n x, ‖bk n x‖ ≤ M) (hLipk : ∀ n, LipschitzWith K (bk n))
    (hbsk : ∀ n, ContDiff ℝ ∞ (bk n)) (hBk : ∀ n, AllDerivativesBounded (bk n))
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {T : ℝ} (hT : 0 ≤ T) (wk : ℕ → C(Icc 0 T,E)) (w : C(Icc 0 T,E)) (xk : ℕ → E) (x : E)
    (hflow : ∀ s ∈ Icc 0 T, Tendsto (fun n => autonomousFlow (hbk n) (hLipk n) hT (xk n) (wk n) s)
      atTop (𝓝 (autonomousFlow hb hLip hT x w s)))
    (hderiv : ∀ (yk : ℕ → E) (y : E), Tendsto yk atTop (𝓝 y) →
      Tendsto (fun n => fderiv ℝ (bk n) (yk n)) atTop (𝓝 (fderiv ℝ b y))) :
    TendstoUniformlyOn (fun n => jacobian (hbk n) (hLipk n) hT (wk n) (xk n))
      (jacobian hb hLip hT w x) atTop (Icc 0 T) := by
  have hDs : ContDiff ℝ ∞ (fderiv ℝ b) := (contDiff_infty_iff_fderiv.mp hbs).2
  have hDks (n : ℕ) : ContDiff ℝ ∞ (fderiv ℝ (bk n)) := (contDiff_infty_iff_fderiv.mp (hbsk n)).2
  obtain ⟨K₁,hDb⟩ := hB.fderiv.lipschitz (hDs.differentiable (by simp))
  have hk (n : ℕ) : ∃ K₁ : ℝ≥0, LipschitzWith K₁ (fderiv ℝ (bk n)) :=
    (hBk n).fderiv.lipschitz ((hDks n).differentiable (by simp))
  choose K₁k hDbk using hk
  exact jacobian_tendstoUniformlyOn hbk hLipk (fun n => (hbsk n).differentiable (by simp)) hDbk
    hb hLip (hbs.differentiable (by simp)) hDb hT wk w xk x hflow hderiv

/-- Locally uniform drift approximation implies convergence of the actual
initial Jacobian, uniformly on every finite time interval. The convergence
assumption concerns only the drifts and their moving-point first derivatives. -/
theorem jacobian_tendstoUniformlyOn_of_locallyUniform_boundedSmooth
    {bk : ℕ → E → E} {b : E → E} {M K : ℝ≥0}
    (hbk : ∀ n x, ‖bk n x‖ ≤ M) (hLipk : ∀ n, LipschitzWith K (bk n))
    (hbsk : ∀ n, ContDiff ℝ ∞ (bk n)) (hBk : ∀ n, AllDerivativesBounded (bk n))
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T,E)) (x : E)
    (happrox : TendstoLocallyUniformly bk b atTop)
    (hderiv : ∀ (yk : ℕ → E) (y : E), Tendsto yk atTop (𝓝 y) →
      Tendsto (fun n => fderiv ℝ (bk n) (yk n)) atTop (𝓝 (fderiv ℝ b y))) :
    TendstoUniformlyOn (fun n => jacobian (hbk n) (hLipk n) hT w x)
      (jacobian hb hLip hT w x) atTop (Icc 0 T) := by
  apply jacobian_tendstoUniformlyOn_of_boundedSmooth hbk hLipk hbsk hBk hb hLip hbs hB hT
    (fun _ => w) w (fun _ => x) x _ hderiv
  intro s hs
  exact finiteTrajectory_tendsto_of_locallyUniform_drift (fun n _ => hLipk n)
    (BoundedFlow.noiseExtension_continuous hT w).continuousOn
    (fun n => BoundedFlow.flow_trajectory (v := fun _ : ℝ => bk n)
      ((hLipk n).continuous.comp continuous_snd) (fun _ => hbk n) (fun _ => hLipk n) hT x w)
    (BoundedFlow.flow_trajectory (v := fun _ : ℝ => b)
      (hLip.continuous.comp continuous_snd) (fun _ => hb) (fun _ => hLip) hT x w)
    (happrox.comp Prod.snd continuous_snd) hs

/-- Fixed-time operator-norm convergence of the actual selected-flow derivative. -/
theorem fderiv_flow_tendsto_of_locallyUniform_boundedSmooth
    {bk : ℕ → E → E} {b : E → E} {M K : ℝ≥0}
    (hbk : ∀ n x, ‖bk n x‖ ≤ M) (hLipk : ∀ n, LipschitzWith K (bk n))
    (hbsk : ∀ n, ContDiff ℝ ∞ (bk n)) (hBk : ∀ n, AllDerivativesBounded (bk n))
    (hb : ∀ x, ‖b x‖ ≤ M) (hLip : LipschitzWith K b)
    (hbs : ContDiff ℝ ∞ b) (hB : AllDerivativesBounded b)
    {T : ℝ} (hT : 0 ≤ T) (w : C(Icc 0 T,E)) (x : E)
    (happrox : TendstoLocallyUniformly bk b atTop)
    (hderiv : ∀ (yk : ℕ → E) (y : E), Tendsto yk atTop (𝓝 y) →
      Tendsto (fun n => fderiv ℝ (bk n) (yk n)) atTop (𝓝 (fderiv ℝ b y)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => fderiv ℝ (fun y => autonomousFlow (hbk n) (hLipk n) hT y w t) x)
      atTop (𝓝 (fderiv ℝ (fun y => autonomousFlow hb hLip hT y w t) x)) := by
  simpa only [jacobian,projIcc_of_mem _ ht] using
    (jacobian_tendstoUniformlyOn_of_locallyUniform_boundedSmooth hbk hLipk hbsk hBk
      hb hLip hbs hB hT w x happrox hderiv).tendsto_at ht

end SharpWasserstein.FlowJacobianDrift
